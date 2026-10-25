#!/usr/bin/env python3
import os
import subprocess
from pathlib import Path
import yaml

PORTS_TO_FREE = [8080, 10080, 20080]


def free_ports(ports):
    for p in ports:
        try:
            result = subprocess.run(
                ["lsof", "-ti", f"TCP:{p}"],
                stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL,
                text=True,
                check=False,
            )
            pids = [x for x in result.stdout.strip().split("\n") if x]
            for pid in pids:
                subprocess.run(
                    ["kill", "-9", pid],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    check=False,
                )
        except Exception:
            # Best-effort; don't block the job if lsof/kill fails.
            pass


def get_node_ip():
    try:
        # Keep behavior consistent with your original script.
        return subprocess.check_output([ "hostname", '-i'], text=True).strip()
    except Exception:
        return "127.0.0.1"


def load_yaml_dict(path: Path) -> dict:
    if not path.exists():
        return {}
    try:
        with path.open("r") as f:
            data = yaml.safe_load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        # If the file is malformed, don’t crash—start from an empty dict.
        return {}


def write_yaml_dict(path: Path, data: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as f:
        yaml.safe_dump(data, f, sort_keys=False)


def set_nested_base_url(config: dict, base_url: str) -> dict:
    # Ensures config["sandbox_fusion"]["base_url"] exists and is set.
    sandbox_fusion = config.get("sandbox_fusion")
    if not isinstance(sandbox_fusion, dict):
        sandbox_fusion = {}
        config["sandbox_fusion"] = sandbox_fusion
    sandbox_fusion["base_url"] = base_url
    return config


def main():
    # Environment setup
    env = os.environ.copy()
    env.setdefault("PORT", "10080")  # default to 10080 if not provided
    port = env["PORT"]

    PROJECT = env.get("PROJECT") or os.getenv("PROJECT")
    if not PROJECT:
        raise RuntimeError("PROJECT not found in environment (PROJECT is missing)")

    HOME = env.get("HOME", str(Path.home()))
    SCRATCH = env.get("SCRATCH", os.path.join(PROJECT, "scratch"))
    SIF_PATH = os.path.join(PROJECT, "sandbox", "code_sandbox_server.sif")

    # This is the ONLY yaml we will create/modify now:
    YAML_PATH = Path(f"{PROJECT}/ecp_lpar/configs/localhost.yaml")

    # Free up ports if already used
    free_ports(PORTS_TO_FREE)

    # Get node IP
    node_ip = get_node_ip()

    # Preserve your SLURM check (even though we no longer create sf_{jobid}.yaml)
    jobid = env.get("SLURM_JOB_ID")
    if not jobid:
        raise RuntimeError("Job ID not found in environment (SLURM_JOB_ID is missing)")

    # Construct URL (per your request, this should go into sandbox_fusion.base_url)
    sandbox_fusion_base_url = f"http://{node_ip}:{port}/run_code"

    # Load/update/write YAML_PATH
    cfg = load_yaml_dict(YAML_PATH)
    cfg = set_nested_base_url(cfg, sandbox_fusion_base_url)
    write_yaml_dict(YAML_PATH, cfg)

    # Paths
    BASE_DIR = Path(__file__).resolve().parent

    # Build the Apptainer exec command (unchanged behavior)
    command = [
        "apptainer",
        "exec",
        "--env",
        f"PORT={port}",
        "--env",
        "OPENBLAS_NUM_THREADS=1",
        "--env",
        "OMP_NUM_THREADS=1",
        "--bind",
        f"{HOME}:{HOME}",
        "--bind",
        f"{SCRATCH}:{SCRATCH}",
        "--bind",
        f"{PROJECT}:{PROJECT}",
        SIF_PATH,
        "make",
        "run-online",
    ]

    # Launch the Apptainer container
    subprocess.run(command, env=env, cwd=str(BASE_DIR), check=False)


if __name__ == "__main__":
    main()
