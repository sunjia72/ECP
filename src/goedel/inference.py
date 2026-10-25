#!/usr/bin/env python3
"""
Multi-node Ray + vLLM inference with:
- SLURM-wide brute-force per-user GPU process killer from the driver
- Inferred tensor parallel layout for 8B/32B Goedel models on 4-GPU nodes
- Dynamic scheduling (work stealing) to reduce idle time and handle slow/fast nodes
- Bounded in-worker vLLM request queues
- Pass@N duplicate prompt grouping via SamplingParams(n=N)
- Intermediate checkpointing:
    * Driver: after EVERY shard
    * Worker: after every checkpoint_interval generated samples

Notes:
- This script intentionally DROPS the single-node path to reduce length.
- The brute-force GPU killer can terminate other GPU jobs owned by the same UNIX user.
"""

import os
import sys
import json
import argparse
import random
import subprocess
import signal
import time
import gc
import shutil
from collections import OrderedDict, deque
from string import Template
from typing import Any, Dict, List, Optional, Tuple
import math
import ray
from tqdm import tqdm
from transformers import AutoTokenizer
from vllm import LLM, SamplingParams
from vllm.sampling_params import RequestOutputKind

from jload import jsave
from src.goedel.utils import (
    get_error_str,
    load_data_for_correction,
    replace_final_by_suffix,
    DeepSeekCoTHandler,
    DeepSeekNonCoTHandler,
    KiminaCoTHandler,
)

DEFAULT_MAX_MODEL_LEN = 30000
MAX_INPUT_TOKENS = 5000

# ============================================================
# SLURM-WIDE BRUTE FORCE GPU CLEANUP (PER-USER) ACROSS NODES
# ============================================================

GPU_CLEANUP_REMOTE_TEMPLATE = Template(
    """#!/usr/bin/env python3
import os
import subprocess
import signal
import time

GRACE_SECONDS = $GRACE_SECONDS
SAME_UID_ONLY = $SAME_UID_ONLY

def list_gpu_processes():
    try:
        out = subprocess.check_output(
            ["nvidia-smi",
             "--query-compute-apps=pid,used_memory,name",
             "--format=csv,noheader,nounits"],
            encoding="utf-8",
            stderr=subprocess.DEVNULL,
        )
    except Exception:
        return []

    procs = []
    for line in out.strip().splitlines():
        if not line.strip():
            continue
        parts = [p.strip() for p in line.split(",")]
        if len(parts) != 3:
            continue
        pid_str, mem_str, name = parts
        try:
            pid = int(pid_str)
            mem_mb = int(mem_str)
        except ValueError:
            continue

        uid = None
        try:
            with open(f"/proc/{pid}/status", "r", encoding="utf-8", errors="ignore") as f:
                for l in f:
                    if l.startswith("Uid:"):
                        toks = l.split()
                        if len(toks) >= 2:
                            uid = int(toks[1])
                        break
        except Exception:
            pass

        procs.append({"pid": pid, "mem_mb": mem_mb, "name": name, "uid": uid})
    return procs


def main():
    my_pid = os.getpid()
    my_uid = os.getuid()

    procs = list_gpu_processes()
    if not procs:
        return

    victims = []
    for p in procs:
        pid = p["pid"]
        if pid == my_pid:
            continue
        if SAME_UID_ONLY and p.get("uid") is not None and p["uid"] != my_uid:
            continue
        victims.append(pid)

    if not victims:
        return

    print(f"[REMOTE GPU CLEANUP] Found {len(victims)} GPU processes to kill.")
    for sig, label in ((signal.SIGTERM, "SIGTERM"), (signal.SIGKILL, "SIGKILL")):
        print(f"[REMOTE GPU CLEANUP] Sending {label} to victims...")
        for pid in victims:
            try:
                os.kill(pid, sig)
            except ProcessLookupError:
                continue
            except PermissionError:
                print(f"[REMOTE GPU CLEANUP] PermissionError for {label} pid={pid}")
                continue
        if label == "SIGTERM":
            time.sleep(GRACE_SECONDS)


if __name__ == "__main__":
    main()
"""
)


def _get_shared_job_cleanup_dir() -> str:
    try:
        here = os.path.abspath(os.path.dirname(__file__))
        repo_root = os.path.abspath(os.path.join(here, "..", ".."))
    except NameError:
        repo_root = os.getcwd()
    shared_dir = os.path.join(repo_root, "cache", "gpu_cleanup")
    os.makedirs(shared_dir, exist_ok=True)
    return shared_dir


def gpu_cleanup_all_nodes(grace_seconds: float = 3.0, same_uid_only: bool = True) -> None:
    slurm_jobid = os.environ.get("SLURM_JOB_ID")
    slurm_nnodes = os.environ.get("SLURM_NNODES")

    script_dir = _get_shared_job_cleanup_dir()
    script_tag = slurm_jobid or "local"
    script_path = os.path.join(script_dir, f"gpu_cleanup_job_{script_tag}.py")

    remote_script = GPU_CLEANUP_REMOTE_TEMPLATE.substitute(
        GRACE_SECONDS=grace_seconds,
        SAME_UID_ONLY="True" if same_uid_only else "False",
    )
    with open(script_path, "w", encoding="utf-8") as f:
        f.write(remote_script)
    try:
        os.chmod(script_path, 0o755)
    except Exception:
        pass

    print(
        f"[GPU CLEANUP] per-user brute-force via {script_path} "
        f"(SLURM_JOB_ID={slurm_jobid}, SLURM_NNODES={slurm_nnodes})"
    )

    if slurm_nnodes and shutil.which("srun") is not None:
        try:
            subprocess.run(
                [
                    "srun",
                    f"--nodes={slurm_nnodes}",
                    f"--ntasks={slurm_nnodes}",
                    "--ntasks-per-node=1",
                    "--overlap",
                    "--cpu-bind=none",
                    "python",
                    script_path,
                ],
                check=False,
            )
            return
        except Exception as e:
            print(f"[GPU CLEANUP] srun failed ({e}); fallback local-only.")

    try:
        subprocess.run(["python", script_path], check=False)
    except Exception as e:
        print(f"[GPU CLEANUP] local cleanup failed: {e}")


# ============================================================
# RESUME / CHECKPOINT HELPERS
# ============================================================

def dedup_by_key(records: List[Dict[str, Any]], key: str = "problem_id") -> List[Dict[str, Any]]:
    seen = {}
    for r in records:
        if isinstance(r, dict) and r.get(key) is not None:
            seen[r[key]] = r
    return list(seen.values())


def _text_is_nonempty(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _has_inference_attempt_payload(record: Dict[str, Any]) -> bool:
    return any(key in record for key in ("model_output", "full_code", "inference_error"))


def inference_record_is_complete(record: Dict[str, Any]) -> bool:
    """Return True for records that should be skipped during resume.

    Empty generations, missing code blocks, and explicit inference errors are
    terminal failed samples for the prover pipeline.  They should be counted as
    completed attempts, not regenerated indefinitely.
    """
    if not isinstance(record, dict) or not record.get("problem_id"):
        return False
    return _has_inference_attempt_payload(record)


def _completion_index(completion: Any, fallback_idx: int) -> int:
    raw_idx = getattr(completion, "index", fallback_idx)
    try:
        return int(raw_idx)
    except (TypeError, ValueError):
        return fallback_idx


def _completion_snapshot(completion: Any) -> Dict[str, Any]:
    token_ids = list(getattr(completion, "token_ids", []) or [])
    return {
        "text": getattr(completion, "text", "") or "",
        "token_ids": token_ids,
        "finish_reason": getattr(completion, "finish_reason", None),
        "stop_reason": getattr(completion, "stop_reason", None),
    }


def accumulate_completion_outputs(
    output: Any,
    completion_cache: Dict[int, Dict[str, Any]],
    token_counts: Optional[Dict[int, int]] = None,
) -> int:
    """Accumulate vLLM completion outputs across step() calls.

    vLLM can emit different completion indexes before the request-level
    ``finished`` flag is set. Dropping those intermediate outputs loses
    samples when SamplingParams(n > 1).
    """
    new_token_count = 0
    for fallback_idx, completion in enumerate(getattr(output, "outputs", []) or []):
        idx = _completion_index(completion, fallback_idx)
        snapshot = _completion_snapshot(completion)
        completion_cache[idx] = snapshot
        if token_counts is not None:
            token_len = len(snapshot["token_ids"])
            previous_len = token_counts.get(idx, 0)
            if token_len > previous_len:
                new_token_count += token_len - previous_len
                token_counts[idx] = token_len
    return new_token_count


def missing_completion_indexes(completion_cache: Dict[int, Dict[str, Any]], expected_n: int) -> List[int]:
    return [idx for idx in range(expected_n) if idx not in completion_cache]


def _code_record_from_existing_record(record: Dict[str, Any]) -> Dict[str, Any]:
    mh = record.get("messages_history_for_this_attempt") or record.get("messages_history_list")
    out = {
        "problem_id": record.get("problem_id"),
        "origin_problem_id": record.get("origin_problem_id"),
        "id_maps": record.get("id_maps"),
        "formal_statement": record.get("formal_statement"),
        "model_input": record.get("model_input"),
        "messages_history_list": mh,
        "model_output": record.get("model_output"),
        "full_code": record.get("full_code"),
    }
    for key in (
        "inference_error",
        "token_nums",
        "expected_completion_count",
        "observed_completion_indexes",
        "generation_finish_reason",
        "generation_stop_reason",
        "generation_token_count",
    ):
        if key in record:
            out[key] = record[key]
    return out


def load_existing_outputs(output_dir: str, records_suffix: str):
    """
    Loads driver outputs + worker checkpoints (if any) and returns:
      existing_records, existing_codes, completed_ids
    """
    existing_records_raw: List[Dict[str, Any]] = []
    existing_codes_raw: List[Dict[str, Any]] = []

    def _try_load(path: str, target_list: List[Dict[str, Any]]):
        if not os.path.exists(path):
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, list):
                target_list.extend(data)
            else:
                print(f"[RESUME] {path} not a list; ignored.")
        except Exception as e:
            print(f"[RESUME] failed loading {path}: {e}")

    main_records_path = os.path.join(output_dir, f"full_records{records_suffix}.json")
    main_codes_path = os.path.join(output_dir, f"to_inference_codes{records_suffix}.json")
    _try_load(main_records_path, existing_records_raw)
    _try_load(main_codes_path, existing_codes_raw)

    ckpt_dir = os.path.join(output_dir, "checkpoints")
    if os.path.isdir(ckpt_dir):
        for fname in os.listdir(ckpt_dir):
            path = os.path.join(ckpt_dir, fname)
            if fname.endswith(f"records{records_suffix}.json"):
                _try_load(path, existing_records_raw)
            elif fname.endswith(f"codes{records_suffix}.json"):
                _try_load(path, existing_codes_raw)

    existing_records = dedup_by_key(existing_records_raw, key="problem_id")
    existing_codes = dedup_by_key(existing_codes_raw, key="problem_id")

    # Reconstruct codes from records if needed
    if existing_records and not existing_codes:
        reconstructed = [
            _code_record_from_existing_record(r)
            for r in existing_records
            if r.get("problem_id")
        ]
        existing_codes = dedup_by_key(reconstructed, key="problem_id")
        print(f"[RESUME] reconstructed {len(existing_codes)} code entries from records.")

    valid_completed_ids = {
        r["problem_id"]
        for r in existing_records
        if inference_record_is_complete(r)
    }
    dropped_records = len(existing_records) - len(valid_completed_ids)
    if dropped_records:
        print(
            f"[RESUME] dropping {dropped_records} incomplete/error record(s); "
            "they will be regenerated."
        )
    existing_records = [r for r in existing_records if r.get("problem_id") in valid_completed_ids]
    existing_codes = [c for c in existing_codes if c.get("problem_id") in valid_completed_ids]
    existing_code_ids = {
        c.get("problem_id")
        for c in existing_codes
        if isinstance(c, dict) and c.get("problem_id")
    }
    missing_code_records = [
        _code_record_from_existing_record(r)
        for r in existing_records
        if r.get("problem_id") and r.get("problem_id") not in existing_code_ids
    ]
    if missing_code_records:
        existing_codes = dedup_by_key(existing_codes + missing_code_records, key="problem_id")
        print(f"[RESUME] reconstructed {len(missing_code_records)} missing code entries from records.")
    completed_ids = valid_completed_ids
    print(
        f"[RESUME] loaded {len(existing_records)} records, {len(existing_codes)} codes, "
        f"{len(completed_ids)} completed ids."
    )
    return existing_records, existing_codes, completed_ids


def _shard_group_key(item: Dict[str, Any]) -> str:
    """
    Keep duplicated samples for the same prompt together when sharding.
    Round 0 duplicates share origin_problem_id; correction duplicates share
    last_problem_id.
    """
    return str(item.get("last_problem_id") or item.get("origin_problem_id") or item.get("problem_id"))


def make_global_shards(items: List[Dict[str, Any]], shard_size: int) -> List[List[Dict[str, Any]]]:
    if shard_size <= 0:
        return [items]

    grouped_runs: List[List[Dict[str, Any]]] = []
    current_run: List[Dict[str, Any]] = []
    current_key = None
    for item in items:
        key = _shard_group_key(item)
        if current_run and key != current_key:
            grouped_runs.append(current_run)
            current_run = []
        current_run.append(item)
        current_key = key
    if current_run:
        grouped_runs.append(current_run)

    shards: List[List[Dict[str, Any]]] = []
    current_shard: List[Dict[str, Any]] = []
    for run in grouped_runs:
        if current_shard and len(current_shard) + len(run) > shard_size:
            shards.append(current_shard)
            current_shard = []
        current_shard.extend(run)
    if current_shard:
        shards.append(current_shard)
    return shards


def infer_tensor_parallel_size(model_path: str, gpus_per_node: int) -> int:
    model_lower = str(model_path).lower()
    if "32b" in model_lower:
        preferred = 4
    elif "8b" in model_lower:
        preferred = 1
    else:
        preferred = 1

    if gpus_per_node <= 0:
        raise ValueError("--gpu must be a positive number of GPUs per node.")
    if gpus_per_node < preferred:
        print(
            f"[GPU layout] requested model looks like it prefers tp={preferred}, "
            f"but only {gpus_per_node} GPU(s) per node were provided; using tp={gpus_per_node}."
        )
        return gpus_per_node
    return preferred


def infer_num_workers(physical_nodes: int, gpus_per_node: int, tensor_parallel_size: int) -> int:
    replicas_per_node = max(1, gpus_per_node // tensor_parallel_size)
    return max(1, physical_nodes * replicas_per_node)


def infer_max_output_tokens(max_model_len: int) -> int:
    max_output_tokens = int(max_model_len) - MAX_INPUT_TOKENS
    if max_output_tokens <= 0:
        raise ValueError(
            f"--max_model_len must be greater than MAX_INPUT_TOKENS={MAX_INPUT_TOKENS}; "
            f"got {max_model_len}."
        )
    return max_output_tokens


def make_sampling_params(args, n: int) -> SamplingParams:
    params = SamplingParams(
        temperature=args.temp,
        max_tokens=infer_max_output_tokens(args.max_model_len),
        top_p=0.95,
        n=n,
    )
    params.output_kind = RequestOutputKind.CUMULATIVE
    return params


# ============================================================
# HANDLER / MODEL
# ============================================================

def build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser()
    p.add_argument("--input_path", default="", type=str)
    p.add_argument(
        "--model_path",
        default="/scratch/gpfs/yl7690/models/Translator_Qwen2.5-Coder-32B_numina_sonnet_130K_translator_Epoch2_LR1e-4",
        type=str,
    )
    p.add_argument(
        "--output_dir",
        default="/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/translator",
        type=str,
    )
    p.add_argument("--split", default="none", type=str)
    p.add_argument("--n", default=32, type=int)
    p.add_argument(
        "--max_model_len",
        default=DEFAULT_MAX_MODEL_LEN,
        type=int,
        help=(
            "vLLM total sequence budget. Prover prompts are hard-capped at "
            f"{MAX_INPUT_TOKENS} tokens; generated output is capped at "
            f"max_model_len - {MAX_INPUT_TOKENS}."
        ),
    )
    p.add_argument(
        "--inference_handler",
        type=str,
        choices=["dpskcot", "dpsknoncot", "kiminacot"],
        required=True,
    )
    p.add_argument("--trunck", default=1, type=int)  # kept for compatibility
    p.add_argument("--gpu", default=4, type=int, help="GPUs per physical node. Tensor parallelism is inferred.")
    p.add_argument("--node", default=1, type=int, help="Number of physical Ray nodes.")
    p.add_argument("--error_thres", default=True)
    p.add_argument("--temp", default=1.0, type=float)
    p.add_argument("--base_output_template", default="qwen", type=str)
    p.add_argument("--correction_round", type=int, default=0)
    p.add_argument("--previous_run_output_dir", type=str, default="")
    # New: shard size for dynamic scheduling
    p.add_argument("--shard_size", type=int, default=0, help="0=auto, else fixed size.")
    p.add_argument("--max_inflight_requests", type=int, default=64)
    p.add_argument("--checkpoint_interval", type=int, default=32)
    p.add_argument("--gpu_memory_utilization", type=float, default=0.9)
    p.add_argument("--max_num_seqs", type=int, default=0, help="0 lets vLLM choose.")
    p.add_argument("--max_num_batched_tokens", type=int, default=0, help="0 lets vLLM choose.")
    p.add_argument("--progress_log_interval", type=float, default=30.0)
    p.add_argument("--disable_prefix_caching", action="store_true")
    p.add_argument("--disable_chunked_prefill", action="store_true")
    return p


def build_handler(args):
    if args.inference_handler == "dpskcot":
        return DeepSeekCoTHandler()
    if args.inference_handler == "dpsknoncot":
        return DeepSeekNonCoTHandler()
    if args.inference_handler == "kiminacot":
        return KiminaCoTHandler()
    raise ValueError(f"Unknown inference_handler: {args.inference_handler}")


def build_model(args, seed: int) -> LLM:
    llm_kwargs = {
        "model": args.model_path,
        "seed": seed,
        "trust_remote_code": True,
        "max_model_len": args.max_model_len,
        "tensor_parallel_size": args.tensor_parallel_size,
        "gpu_memory_utilization": args.gpu_memory_utilization,
        "enable_prefix_caching": not args.disable_prefix_caching,
        "enable_chunked_prefill": not args.disable_chunked_prefill,
    }
    if args.max_num_seqs > 0:
        llm_kwargs["max_num_seqs"] = args.max_num_seqs
    if args.max_num_batched_tokens > 0:
        llm_kwargs["max_num_batched_tokens"] = args.max_num_batched_tokens
    return LLM(**llm_kwargs)


# ============================================================
# RAY WORKER
# ============================================================

@ray.remote
class InferenceWorker:
    def __init__(self, args, seed: int, worker_idx: int):
        self.args = args
        self.worker_idx = worker_idx
        self.seed = seed + worker_idx
        random.seed(self.seed)

        self.records_suffix = f"_corr{args.correction_round}" if args.correction_round > 0 else ""
        self.checkpoint_dir = os.path.join(args.output_dir, "checkpoints")
        os.makedirs(self.checkpoint_dir, exist_ok=True)

        print(f"[Worker {worker_idx}] tokenizer init...")
        self.tokenizer = AutoTokenizer.from_pretrained(args.model_path, trust_remote_code=True)

        print(f"[Worker {worker_idx}] handler init...")
        self.handler = build_handler(args)

        print(f"[Worker {worker_idx}] model init (tp={args.tensor_parallel_size})...")
        self.model = build_model(args, self.seed)
        self.max_prompt_len = MAX_INPUT_TOKENS
        self.max_output_tokens = infer_max_output_tokens(args.max_model_len)
        self.request_counter = 0
        print(
            f"[Worker {worker_idx}] ready. max_prompt_len={self.max_prompt_len}, "
            f"max_output_tokens={self.max_output_tokens}, "
            f"max_inflight_requests={args.max_inflight_requests}"
        )

    def _save_worker_checkpoint(self, processed_records, processed_codes, processed_count, total_items):
        rec_path = os.path.join(
            self.checkpoint_dir, f"worker{self.worker_idx}_records{self.records_suffix}.json"
        )
        code_path = os.path.join(
            self.checkpoint_dir, f"worker{self.worker_idx}_codes{self.records_suffix}.json"
        )
        jsave(dedup_by_key(processed_records, "problem_id"), rec_path)
        jsave(dedup_by_key(processed_codes, "problem_id"), code_path)
        print(f"[Worker {self.worker_idx}] checkpoint {processed_count}/{total_items} -> {rec_path}")

    def _make_row(self, item_data: Dict[str, Any]) -> Dict[str, Any]:
        item_data = item_data.copy()
        item_data["formal_statement"] = replace_final_by_suffix(
            item_data["formal_statement"], ":= by sorry"
        )

        if self.args.correction_round > 0:
            error_str = get_error_str(
                item_data.get("compiled_code_that_failed_in_prev_round", ""),
                item_data.get("errors_for_compiled_code_from_prev_round", {}),
                self.args.error_thres,
            )
            prompt_str, messages_for_this = self.handler.generate_correction_prompt(
                lean4_code_original_stmt=item_data["formal_statement"],
                history_messages_from_prev_round=item_data.get("history_messages_from_prev_round_for_new_prompt", []),
                prev_round_llm_raw_output=item_data.get("prev_round_llm_raw_output_for_new_prompt", ""),
                error_message_for_prev_round=error_str,
                tokenizer=self.tokenizer,
                current_correction_round_num=self.args.correction_round,
                unsolved_goals_restart_hint=item_data.get("unsolved_goals_restart_hint", False),
            )
        else:
            prompt_str, messages_for_this = self.handler.prover_inference(
                item_data["formal_statement"], self.tokenizer
            )

        return {
            "token_nums": len(self.tokenizer.tokenize(prompt_str)),
            "prompt": prompt_str,
            "messages": messages_for_this,
            "item": item_data,
        }

    def _build_request_groups(self, chunk: List[Dict[str, Any]]) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
        groups_by_prompt: "OrderedDict[str, Dict[str, Any]]" = OrderedDict()
        skipped_rows: List[Dict[str, Any]] = []

        for item_data in chunk:
            row = self._make_row(item_data)
            if row["token_nums"] > self.max_prompt_len:
                skipped_rows.append(row)
                continue

            group = groups_by_prompt.get(row["prompt"])
            if group is None:
                group = {
                    "prompt": row["prompt"],
                    "messages": row["messages"],
                    "token_nums": row["token_nums"],
                    "samples": [],
                }
                groups_by_prompt[row["prompt"]] = group
            group["samples"].append(row)

        return list(groups_by_prompt.values()), skipped_rows

    def _code_record_from_item(self, input_item: Dict[str, Any]) -> Dict[str, Any]:
        out = {
            "problem_id": input_item["problem_id"],
            "origin_problem_id": input_item.get("origin_problem_id"),
            "id_maps": input_item.get("id_maps"),
            "formal_statement": input_item["formal_statement"],
            "model_input": input_item["model_input"],
            "messages_history_list": input_item["messages_history_for_this_attempt"],
            "model_output": input_item["model_output"],
            "full_code": input_item["full_code"],
        }
        for key in (
            "inference_error",
            "token_nums",
            "expected_completion_count",
            "observed_completion_indexes",
            "generation_finish_reason",
            "generation_stop_reason",
            "generation_token_count",
        ):
            if key in input_item:
                out[key] = input_item[key]
        return out

    def _finalize_generation(
        self,
        row: Dict[str, Any],
        llm_text: str,
        generation_meta: Optional[Dict[str, Any]] = None,
    ) -> Tuple[Dict[str, Any], Dict[str, Any]]:
        input_item = row["item"].copy()
        input_item["model_input"] = row["prompt"]
        input_item["messages_history_for_this_attempt"] = row["messages"]
        input_item["model_output"] = llm_text
        input_item["token_nums"] = row["token_nums"]
        if generation_meta:
            input_item["generation_finish_reason"] = generation_meta.get("finish_reason")
            input_item["generation_stop_reason"] = generation_meta.get("stop_reason")
            input_item["generation_token_count"] = len(generation_meta.get("token_ids") or [])

        if not _text_is_nonempty(llm_text):
            input_item["full_code"] = "None"
            input_item["inference_error"] = "empty_model_output"
            return input_item, self._code_record_from_item(input_item)

        extracted = self.handler.extrac_code(llm_text)
        if extracted in ("None", None):
            input_item["full_code"] = "None"
        else:
            input_item["full_code"] = self.handler.problem_check(
                input_item["formal_statement"], extracted
            )
        return input_item, self._code_record_from_item(input_item)

    def _finalize_missing_completion(
        self,
        row: Dict[str, Any],
        expected_count: int,
        observed_indexes: List[int],
    ) -> Tuple[Dict[str, Any], Dict[str, Any]]:
        input_item = row["item"].copy()
        input_item["model_input"] = row["prompt"]
        input_item["messages_history_for_this_attempt"] = row["messages"]
        input_item["model_output"] = ""
        input_item["full_code"] = "None"
        input_item["inference_error"] = "missing_completion"
        input_item["token_nums"] = row["token_nums"]
        input_item["expected_completion_count"] = expected_count
        input_item["observed_completion_indexes"] = observed_indexes
        return input_item, self._code_record_from_item(input_item)

    def _finalize_skipped_prompt(self, row: Dict[str, Any], reason: str) -> Tuple[Dict[str, Any], Dict[str, Any]]:
        input_item = row["item"].copy()
        input_item["model_input"] = row["prompt"]
        input_item["messages_history_for_this_attempt"] = row["messages"]
        input_item["model_output"] = ""
        input_item["full_code"] = "None"
        input_item["inference_error"] = reason
        input_item["token_nums"] = row["token_nums"]
        return input_item, self._code_record_from_item(input_item)

    def _add_engine_request(self, group: Dict[str, Any]) -> str:
        request_id = f"{self.worker_idx}-{self.request_counter}"
        self.request_counter += 1
        sampling_params = make_sampling_params(self.args, n=len(group["samples"]))
        self.model.llm_engine.add_request(request_id, group["prompt"], sampling_params)
        return request_id

    def run(self, items: List[Dict[str, Any]]):
        total_items = len(items)
        if total_items == 0:
            return [], []

        all_records: List[Dict[str, Any]] = []
        all_codes: List[Dict[str, Any]] = []
        checkpoint_interval = max(1, int(self.args.checkpoint_interval))
        last_checkpoint_count = 0

        def maybe_checkpoint(force: bool = False):
            nonlocal last_checkpoint_count
            if not all_records:
                return
            if force or len(all_records) - last_checkpoint_count >= checkpoint_interval:
                self._save_worker_checkpoint(
                    processed_records=all_records,
                    processed_codes=all_codes,
                    processed_count=len(all_records),
                    total_items=total_items,
                )
                last_checkpoint_count = len(all_records)

        chunks = self.handler.split_list_into_chunks(items, num_chunks=max(1, self.args.trunck))
        pbar = tqdm(
            total=total_items,
            desc=f"Worker {self.worker_idx} generated",
            dynamic_ncols=True,
            leave=False,
        )

        try:
            for chunk_idx, chunk in enumerate(chunks):
                groups, skipped_rows = self._build_request_groups(chunk)
                print(
                    f"[Worker {self.worker_idx}] chunk {chunk_idx}/{len(chunks)}: "
                    f"{len(chunk)} samples -> {len(groups)} vLLM requests; "
                    f"{len(skipped_rows)} prompt(s) too long"
                )

                for row in skipped_rows:
                    record, code_record = self._finalize_skipped_prompt(
                        row,
                        reason=f"prompt_too_long: {row['token_nums']} > {self.max_prompt_len}",
                    )
                    all_records.append(record)
                    all_codes.append(code_record)
                if skipped_rows:
                    pbar.update(len(skipped_rows))
                    maybe_checkpoint()

                pending_groups = deque(groups)
                in_flight: Dict[str, Dict[str, Any]] = {}
                max_inflight = max(1, int(self.args.max_inflight_requests))
                completion_caches: Dict[str, Dict[int, Dict[str, Any]]] = {}
                request_token_counts: Dict[str, Dict[int, int]] = {}
                total_input_tokens = 0
                total_output_tokens = 0
                stats_started_at = time.time()
                last_progress_log_at = stats_started_at
                progress_log_interval = max(1.0, float(self.args.progress_log_interval))

                while pending_groups or in_flight:
                    while pending_groups and len(in_flight) < max_inflight:
                        group = pending_groups.popleft()
                        request_id = self._add_engine_request(group)
                        in_flight[request_id] = group
                        completion_caches[request_id] = {}
                        request_token_counts[request_id] = {}
                        total_input_tokens += int(group["token_nums"]) * len(group["samples"])

                    step_outputs = self.model.llm_engine.step()
                    now = time.time()
                    for output in step_outputs:
                        request_id = output.request_id
                        total_output_tokens += accumulate_completion_outputs(
                            output,
                            completion_caches.setdefault(request_id, {}),
                            request_token_counts.setdefault(request_id, {}),
                        )

                        if not getattr(output, "finished", False):
                            continue
                        group = in_flight.pop(request_id)
                        completions_by_index = completion_caches.pop(request_id, {})
                        request_token_counts.pop(request_id, None)
                        expected_count = len(group["samples"])
                        observed_indexes = sorted(completions_by_index)
                        missing = missing_completion_indexes(completions_by_index, expected_count)
                        if missing:
                            print(
                                f"[Worker {self.worker_idx}] request {request_id}: "
                                f"missing completion indexes {missing} of {expected_count}; "
                                f"observed={observed_indexes}"
                            )
                        for sample_idx, row in enumerate(group["samples"]):
                            snapshot = completions_by_index.get(sample_idx)
                            if snapshot is None:
                                record, code_record = self._finalize_missing_completion(
                                    row,
                                    expected_count=expected_count,
                                    observed_indexes=observed_indexes,
                                )
                            else:
                                record, code_record = self._finalize_generation(
                                    row,
                                    snapshot.get("text", ""),
                                    generation_meta=snapshot,
                                )
                            all_records.append(record)
                            all_codes.append(code_record)
                        pbar.update(len(group["samples"]))
                        maybe_checkpoint()

                    if now - last_progress_log_at >= progress_log_interval:
                        elapsed = max(1e-6, now - stats_started_at)
                        input_tps = total_input_tokens / elapsed
                        output_tps = total_output_tokens / elapsed
                        postfix = (
                            f"active={len(in_flight)} queued={len(pending_groups)} "
                            f"input={input_tps:.2f} toks/s output={output_tps:.2f} toks/s"
                        )
                        pbar.set_postfix_str(postfix)
                        print(
                            f"[Worker {self.worker_idx}] progress {pbar.n}/{total_items}; "
                            f"{postfix}"
                        )
                        last_progress_log_at = now

                print(f"[Worker {self.worker_idx}] finished chunk {chunk_idx}/{len(chunks)}")

            maybe_checkpoint(force=True)
        finally:
            pbar.close()

        return all_records, all_codes

    def shutdown(self):
        try:
            engine = (
                getattr(self.model, "llm_engine", None)
                or getattr(self.model, "engine", None)
                or getattr(self.model, "_engine", None)
            )
            if engine is not None and hasattr(engine, "shutdown"):
                print(f"[Worker {self.worker_idx}] engine.shutdown()...")
                engine.shutdown()
        except Exception as e:
            print(f"[Worker {self.worker_idx}] engine shutdown failed: {e}")
        finally:
            self.model = None
            try:
                gc.collect()
                import torch
                if torch.cuda.is_available():
                    torch.cuda.empty_cache()
            except Exception as e:
                print(f"[Worker {self.worker_idx}] cuda empty_cache failed: {e}")

            print(f"[Worker {self.worker_idx}] shutdown complete.")


# ============================================================
# MAIN (MULTI-NODE ONLY)
# ============================================================

def main():
    args = build_arg_parser().parse_args()
    assert args.node > 0, "--node must be > 0"
    args.max_output_tokens = infer_max_output_tokens(args.max_model_len)
    args.tensor_parallel_size = infer_tensor_parallel_size(args.model_path, args.gpu)
    args.num_workers = infer_num_workers(args.node, args.gpu, args.tensor_parallel_size)
    replicas_per_node = max(1, args.gpu // args.tensor_parallel_size)
    print(
        f"[GPU layout] model={args.model_path}; physical_nodes={args.node}; "
        f"gpus_per_node={args.gpu}; tp={args.tensor_parallel_size}; "
        f"replicas_per_node={replicas_per_node}; ray_workers={args.num_workers}; "
        f"max_model_len={args.max_model_len}; max_input_tokens={MAX_INPUT_TOKENS}; "
        f"max_output_tokens={args.max_output_tokens}"
    )

    if args.correction_round == 0:
        assert args.input_path, "--input_path is required for correction_round=0"

    seed = random.randint(1, 999999)

    os.makedirs(args.output_dir, exist_ok=True)
    records_suffix = f"_corr{args.correction_round}" if args.correction_round > 0 else ""
    out_records = os.path.join(args.output_dir, f"full_records{records_suffix}.json")
    out_codes = os.path.join(args.output_dir, f"to_inference_codes{records_suffix}.json")

    # Resume
    existing_records, existing_codes, completed_ids = load_existing_outputs(args.output_dir, records_suffix)
    if existing_records or existing_codes:
        # Persist merged checkpoint-loaded state before workers can overwrite
        # per-worker checkpoint files in this resumed run.
        jsave(dedup_by_key(existing_records, "problem_id"), out_records)
        jsave(dedup_by_key(existing_codes, "problem_id"), out_codes)

    # Build data
    handler = build_handler(args)
    items: List[Dict[str, Any]] = []

    prev_dir = args.previous_run_output_dir or (args.output_dir if args.correction_round > 0 else "")
    if args.correction_round > 0:
        if not prev_dir:
            print("Error: correction_round>0 but no previous dir resolved.")
            sys.exit(1)
        items = load_data_for_correction(prev_dir, args.correction_round, args.n, args.base_output_template)
    else:
        initial = handler.load_split(args.input_path, args.split)
        for idata_orig in initial:
            origin_id = idata_orig.get("origin_problem_id", idata_orig.get("problem_id", idata_orig.get("name")))
            if not idata_orig.get("formal_statement"):
                continue
            for ij in range(args.n):
                it = idata_orig.copy()
                it["origin_problem_id"] = origin_id
                it["problem_id"] = f"{origin_id}_g{ij}"
                it["id_maps"] = [{"origin_problem_id": origin_id}, {"generation_id": it["problem_id"]}]
                items.append(it)

    # Filter completed
    if completed_ids:
        before = len(items)
        items = [it for it in items if it.get("problem_id") not in completed_ids]
        print(f"[RESUME] skipped {before - len(items)} completed; remaining {len(items)}")

    # If nothing left, just rewrite outputs and exit
    if not items:
        print("[Driver] nothing left to run; writing existing outputs and exit.")
        jsave(dedup_by_key(existing_records, "problem_id"), out_records)
        jsave(dedup_by_key(existing_codes, "problem_id"), out_codes)
        return

    total_items = len(items)
    print(f"[Driver] total items to run: {total_items}")

    print("[Driver] pre-inference brute-force GPU cleanup (all nodes)...")
    gpu_cleanup_all_nodes()

    if args.shard_size > 0:
        shard_size = args.shard_size
    else:
        shard_size = max(1, min(math.ceil(total_items / args.num_workers), 300))

    shards = make_global_shards(items, shard_size=shard_size)
    print(f"[Driver] built {len(shards)} shards @ size~{shard_size}")

    # Ray
    ray.init(address="auto")

    workers: List[Tuple[int, Any]] = []
    pbar = tqdm(total=total_items, desc=f"Global progress (round {args.correction_round})")

    # Start from existing outputs
    all_records = existing_records.copy()
    all_codes = existing_codes.copy()

    try:
        # Create only workers that can receive a shard. This avoids loading
        # idle vLLM replicas for tiny smoke/resume runs.
        active_worker_count = min(args.num_workers, len(shards))
        for worker_idx in range(active_worker_count):
            w = InferenceWorker.options(num_gpus=args.tensor_parallel_size).remote(args, seed, worker_idx)
            workers.append((worker_idx, w))

        # Dynamic scheduling
        next_shard = 0
        pending = []
        ref_to_worker = {}

        # Prime: one shard per worker
        for worker_idx, w in workers:
            if next_shard >= len(shards):
                break
            ref = w.run.remote(shards[next_shard])
            pending.append(ref)
            ref_to_worker[ref] = worker_idx
            next_shard += 1

        # Process as they complete
        while pending:
            done, pending = ray.wait(pending, num_returns=1)
            ref = done[0]
            wid = ref_to_worker.pop(ref)

            recs, codes = ray.get(ref)
            all_records.extend(recs)
            all_codes.extend(codes)

            # progress + driver checkpoint
            pbar.update(len(recs))
            all_records = dedup_by_key(all_records, "problem_id")
            all_codes = dedup_by_key(all_codes, "problem_id")
            jsave(all_records, out_records)
            jsave(all_codes, out_codes)

            # Assign next shard to freed worker
            if next_shard < len(shards):
                w = [ww for (idx, ww) in workers if idx == wid][0]
                ref2 = w.run.remote(shards[next_shard])
                pending.append(ref2)
                ref_to_worker[ref2] = wid
                next_shard += 1

        print(f"[Driver] done. outputs:\n  {out_records}\n  {out_codes}")

    finally:
        pbar.close()
        if workers:
            try:
                ray.get([w.shutdown.remote() for _, w in workers], timeout=120.0)
            except Exception as e:
                print(f"[Driver] warning: worker shutdown issue: {e}")

        print("[Driver] post-inference brute-force GPU cleanup (all nodes)...")
        gpu_cleanup_all_nodes()

        try:
            ray.shutdown()
        except Exception as e:
            print(f"[Driver] warning: ray.shutdown failed: {e}")


if __name__ == "__main__":
    main()
