import subprocess
import time
import requests
import torch
import os
import signal
import sys
from pathlib import Path
import yaml  # pip install pyyaml

print("[vLLM DEBUG] CUDA_VISIBLE_DEVICES:", os.environ.get("CUDA_VISIBLE_DEVICES"))
print("[vLLM DEBUG] torch.cuda.device_count():", torch.cuda.device_count())

# ─── Configuration ──────────────────────────────────────────────────────────────

MODEL_PATH = "Goedel-LM/Goedel-Prover-V2-32B"
HOST = "0.0.0.0"
PORT = 30000

PROJECT_ROOT = Path(os.environ["PROJECT"])


# FIX: use Path, not str "/" str
LOG_DIR = Path("output") / "deploy" / "logs"
LOG_DIR.mkdir(parents=True, exist_ok=True)
LOGFILE = str(LOG_DIR / "goedel32b.log")

# vLLM distributed backend (Ray if available, else mp)
DISTRIBUTED_BACKEND = 'mp'

API_URL = f"http://127.0.0.1:{PORT}/v1/models"

YAML_FILES = [
    Path("configs") / "localhost.yaml",
]

TENSOR_PARALLEL_SIZE = 4


# Prefer a sane long-context default for GPT-OSS; override via env if you want
MAX_MODEL_LEN = int(os.getenv("VLLM_MAX_MODEL_LEN", "30000"))

# IMPORTANT CHANGE:
# Disable GPT-OSS reasoning/tool parsers to avoid frequent 400s from output parsing.
# (Your client can still call /v1/chat/completions normally.)
ENABLE_TOOL_REASONING_PARSERS = True

# Which LLM sections to update/create



def is_server_running() -> bool:
    """Check if a vLLM OpenAI-compatible server is already running on localhost:PORT."""
    try:
        r = requests.get(API_URL, timeout=2)
        return r.status_code == 200
    except requests.exceptions.RequestException:
        return False


def kill_existing_server() -> None:
    """
    Search for any processes that look like 'vllm.entrypoints.openai.api_server'
    and kill them (SIGKILL). This ensures the port is free.
    """
    print("[!] Searching for running vLLM servers to kill...")
    try:
        result = subprocess.run(["ps", "aux"], capture_output=True, text=True, check=False)
        lines = result.stdout.strip().split("\n")
        for line in lines:
            if "vllm.entrypoints.openai.api_server" in line and "python" in line:
                parts = line.split()
                pid = int(parts[1])
                print(f"[✖] Killing PID {pid}")
                os.kill(pid, signal.SIGKILL)
    except Exception as e:
        print(f"[⚠] Failed to kill process: {e}")


def get_host_ip() -> str:
    """
    Obtain the primary IP address using `hostname -i`.
    Fallback to 127.0.0.1 if anything goes wrong.
    """
    try:
        out = subprocess.check_output(["hostname", "-i"], text=True).strip()
        ip = out.split()[0]
        print(f"[ℹ] Detected host IP: {ip}")
        return ip
    except Exception as e:
        print(f"[⚠] Failed to get host IP via 'hostname -i': {e}")
        fallback_ip = "127.0.0.1"
        print(f"[ℹ] Falling back to {fallback_ip}")
        return fallback_ip


def _safe_load_yaml(path: Path) -> dict:
    """
    Load YAML if it exists; otherwise return {}.
    If the YAML exists but is empty / invalid / not a dict at the top, return {}.
    """
    if not path.exists():
        return {}

    try:
        text = path.read_text(encoding="utf-8")
        if not text.strip():
            return {}

        data = yaml.safe_load(text)
        if isinstance(data, dict):
            return data

        # If it's not a dict (e.g., list/str/int), we normalize to dict
        print(f"[⚠] YAML top-level is not a dict in {path}. Replacing with an empty dict.")
        return {}
    except Exception as e:
        print(f"[⚠] Failed to read/parse YAML {path}: {e}. Replacing with an empty dict.")
        return {}


def _ensure_section_dict(cfg: dict, section: str) -> dict:
    """
    Ensure cfg[section] exists and is a dict. If missing or wrong type, create/replace it.
    Returns the section dict.
    """
    cur = cfg.get(section)
    if isinstance(cur, dict):
        return cur
    cfg[section] = {}
    return cfg[section]

def update_llm_base_urls(ip: str) -> None:
    """
    Update ONLY prover_llm.base_url in the YAML configs to 'http://{ip}:{PORT}/v1'.

    - If the YAML file does not exist, create it.
    - If prover_llm does not exist or is not a dict, create/replace it.
    - Do NOT touch any other sections or attributes.
    """
    new_base_url = f"http://{ip}:{PORT}/v1"
    print(f"[📝] Setting prover_llm.base_url to: {new_base_url}")

    for yaml_path in YAML_FILES:
        try:
            yaml_path = Path(yaml_path)
            yaml_path.parent.mkdir(parents=True, exist_ok=True)

            cfg = _safe_load_yaml(yaml_path)

            # Ensure prover_llm exists and is a dict
            prover_llm = cfg.get("prover_llm")
            if not isinstance(prover_llm, dict):
                prover_llm = {}
                cfg["prover_llm"] = prover_llm

            # Update ONLY this attribute
            prover_llm["base_url"] = new_base_url

            # Write back
            with yaml_path.open("w", encoding="utf-8") as f:
                yaml.safe_dump(
                    cfg,
                    f,
                    sort_keys=False,
                    default_flow_style=False,
                    allow_unicode=True,
                )

            print(f"[✔] Updated prover_llm.base_url in {yaml_path}")

        except Exception as e:
            print(f"[⚠] Failed to update {yaml_path}: {e}")


def start_vllm_server() -> None:
    """
    Launch the vLLM OpenAI-compatible API server in the foreground.
    This call will block the terminal until the server exits.
    """
    if is_server_running():
        kill_existing_server()
        time.sleep(2)

    print(f"[🚀] Starting vLLM server on {HOST}:{PORT}")
    print(f"[ℹ] max_model_len={MAX_MODEL_LEN} tp={TENSOR_PARALLEL_SIZE} backend={DISTRIBUTED_BACKEND}")
    print(f"[ℹ] parsers_enabled={ENABLE_TOOL_REASONING_PARSERS}")
    print(f"[📄] Logs -> {LOGFILE}")

    command = [
        sys.executable,
        "-m",
        "vllm.entrypoints.openai.api_server",
        "--model",
        MODEL_PATH,
        "--host",
        HOST,
        "--port",
        str(PORT),
        "--max-model-len",
        str(MAX_MODEL_LEN),
        "--tensor-parallel-size",
        str(TENSOR_PARALLEL_SIZE),
        "--distributed-executor-backend",
        DISTRIBUTED_BACKEND,
        "--trust-remote-code",
    ]

    # Optional: enable these ONLY if you really need tool calling / GPT-OSS parsing.
    # Many 400s come from parser strictness.
    if ENABLE_TOOL_REASONING_PARSERS:
        command += [
            "--enable-auto-tool-choice",
            "--tool-call-parser",
            "openai",
            "--reasoning-parser",
            "openai_gptoss",
        ]

    with open(LOGFILE, "w", encoding="utf-8") as log_file:
        process = subprocess.Popen(
            command,
            stdout=log_file,
            stderr=subprocess.STDOUT,
        )
        print(f"[✔] vLLM server launched with PID {process.pid}")
        print("[⏱] Waiting for vLLM server to exit (Ctrl+C to stop)...")

        try:
            process.wait()
        except KeyboardInterrupt:
            print("\n[✋] KeyboardInterrupt received, terminating vLLM server...")
            try:
                process.terminate()
            except Exception:
                pass
            try:
                process.wait(timeout=10)
            except Exception:
                print("[✖] Forcing kill of vLLM server...")
                try:
                    process.kill()
                except Exception:
                    pass

    print("[✔] vLLM server has exited.")


if __name__ == "__main__":
    ip = get_host_ip()
    update_llm_base_urls(ip)
    start_vllm_server()
