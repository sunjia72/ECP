#!/usr/bin/env python3
"""
Commercial-model prover inference for the Goedel pipeline.

This script intentionally mirrors the JSON contract of src.goedel.inference:
  - full_records{_corrK}.json
  - to_inference_codes{_corrK}.json
  - checkpoint files under <output_dir>/checkpoints

Unlike the vLLM path, it does not allocate GPUs, start Ray, or handle
multi-node inference. It expands Pass@N into independent API requests and runs
them with multiprocessing.
"""

from __future__ import annotations

import argparse
import json
import multiprocessing as mp
import os
import random
import sys
import time
from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import requests
from tqdm import tqdm

from src.goedel.utils import (
    DeepSeekCoTHandler,
    DeepSeekNonCoTHandler,
    KiminaCoTHandler,
    get_error_str,
    load_data_for_correction,
    replace_final_by_suffix,
)


OPENAI_RESPONSES_URL = "https://api.openai.com/v1/responses"
OPENROUTER_CHAT_COMPLETIONS_URL = "https://openrouter.ai/api/v1/chat/completions"
MAX_INPUT_TOKENS = 5000
DEFAULT_MAX_MODEL_LEN = 30000
DEFAULT_PARALLEL = os.cpu_count() or 1

OPENROUTER_PREFIXES = (
    "openai/",
    "google/",
    "qwen/",
    "anthropic/",
    "deepseek/",
    "meta-llama/",
    "mistralai/",
    "x-ai/",
    "cohere/",
    "moonshotai/",
)

_WORKER_ARGS: Dict[str, Any] = {}
_WORKER_HANDLER: Any = None
_WORKER_TOKENIZER: Any = None
API_USAGE_METADATA_KEYS = ("api_usage", "api_token_stats")


class CommercialPromptTokenizer:
    """Small tokenizer facade for handlers that expect chat-template methods."""

    def tokenize(self, text: str) -> List[str]:
        if not isinstance(text, str):
            text = str(text)
        return text.split()

    def apply_chat_template(
        self,
        messages: Sequence[Dict[str, Any]],
        tokenize: bool = False,
        add_generation_prompt: bool = True,
        **_: Any,
    ) -> Any:
        rendered_parts: List[str] = []
        for msg in messages or []:
            role = str(msg.get("role", "user")).upper()
            content = msg.get("content", "")
            if not isinstance(content, str):
                content = json.dumps(content, ensure_ascii=False)
            rendered_parts.append(f"{role}:\n{content}")
        if add_generation_prompt:
            rendered_parts.append("ASSISTANT:")
        rendered = "\n\n".join(rendered_parts)
        if tokenize:
            return self.tokenize(rendered)
        return rendered


@dataclass
class PreparedItem:
    item: Dict[str, Any]
    prompt: str
    messages_history: Any
    api_messages: List[Dict[str, str]]
    token_nums: int


def eprint(*args: Any, **kwargs: Any) -> None:
    print(*args, file=sys.stderr, **kwargs)
    sys.stderr.flush()


def safe_write_json(path: str, data: Any) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    os.replace(tmp, path)


def dedup_by_key(records: Iterable[Dict[str, Any]], key: str = "problem_id") -> List[Dict[str, Any]]:
    seen: Dict[str, Dict[str, Any]] = {}
    for record in records:
        if isinstance(record, dict) and record.get(key) is not None:
            seen[str(record[key])] = record
    return list(seen.values())


def strip_api_usage_metadata(record: Dict[str, Any]) -> Dict[str, Any]:
    cleaned = dict(record)
    for key in API_USAGE_METADATA_KEYS:
        cleaned.pop(key, None)
    return cleaned


def _try_load_list(path: str) -> List[Dict[str, Any]]:
    if not os.path.exists(path):
        return []
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            return [row for row in data if isinstance(row, dict)]
        eprint(f"[RESUME] {path} is not a JSON list; ignored.")
    except Exception as exc:
        eprint(f"[RESUME] failed loading {path}: {exc}")
    return []


def load_existing_outputs(output_dir: str, records_suffix: str) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]], set[str]]:
    records_raw: List[Dict[str, Any]] = []
    codes_raw: List[Dict[str, Any]] = []

    records_raw.extend(_try_load_list(os.path.join(output_dir, f"full_records{records_suffix}.json")))
    codes_raw.extend(_try_load_list(os.path.join(output_dir, f"to_inference_codes{records_suffix}.json")))

    ckpt_dir = os.path.join(output_dir, "checkpoints")
    if os.path.isdir(ckpt_dir):
        for fname in sorted(os.listdir(ckpt_dir)):
            path = os.path.join(ckpt_dir, fname)
            if fname.endswith(f"records{records_suffix}.json"):
                records_raw.extend(_try_load_list(path))
            elif fname.endswith(f"codes{records_suffix}.json"):
                codes_raw.extend(_try_load_list(path))

    records = dedup_by_key(records_raw, "problem_id")
    codes = dedup_by_key(codes_raw, "problem_id")

    if records and not codes:
        reconstructed: List[Dict[str, Any]] = []
        for record in records:
            pid = record.get("problem_id")
            if not pid:
                continue
            reconstructed.append(_code_record_from_item(record))
        codes = dedup_by_key(reconstructed, "problem_id")
        eprint(f"[RESUME] reconstructed {len(codes)} code entries from records.")

    if records:
        code_ids = {str(row.get("problem_id")) for row in codes if row.get("problem_id")}
        missing_codes = [
            _code_record_from_item(record)
            for record in records
            if record.get("problem_id") and str(record.get("problem_id")) not in code_ids
        ]
        if missing_codes:
            codes = dedup_by_key(codes + missing_codes, "problem_id")
            eprint(f"[RESUME] reconstructed {len(missing_codes)} missing code entries from records.")

    completed_ids = {str(r["problem_id"]) for r in records if r.get("problem_id")}
    eprint(
        f"[RESUME] loaded {len(records)} records, {len(codes)} codes, "
        f"{len(completed_ids)} completed ids."
    )
    return records, codes, completed_ids


def _is_openai_hosted_model(model: str) -> bool:
    return (model or "").strip().lower().startswith("gpt-5")


def _is_openrouter_model(model: str) -> bool:
    m = (model or "").strip().lower()
    return any(m.startswith(prefix) for prefix in OPENROUTER_PREFIXES)


def infer_backend(model: str) -> str:
    if _is_openrouter_model(model):
        return "openrouter"
    if _is_openai_hosted_model(model):
        return "openai"
    raise ValueError(
        f"Unsupported commercial prover model '{model}'. "
        "Use a gpt-5* OpenAI model, an OpenRouter provider-prefixed model, "
        "or route local prover models through src.goedel.inference."
    )


def build_handler(name: str) -> Any:
    if name == "dpskcot":
        return DeepSeekCoTHandler()
    if name == "dpsknoncot":
        return DeepSeekNonCoTHandler()
    if name == "kiminacot":
        return KiminaCoTHandler()
    raise ValueError(f"Unknown inference_handler: {name}")


def infer_max_output_tokens(max_model_len: int) -> int:
    value = int(max_model_len) - MAX_INPUT_TOKENS
    if value <= 0:
        raise ValueError(
            f"--max_model_len must be greater than {MAX_INPUT_TOKENS}; got {max_model_len}."
        )
    return value


def _sanitize_messages(messages: Any, fallback_prompt: str) -> List[Dict[str, str]]:
    if not isinstance(messages, list) or not messages:
        return [{"role": "user", "content": fallback_prompt}]

    out: List[Dict[str, str]] = []
    for msg in messages:
        if not isinstance(msg, dict):
            continue
        role = str(msg.get("role", "user")).lower()
        if role not in {"system", "user", "assistant"}:
            role = "user"
        content = msg.get("content", "")
        if not isinstance(content, str):
            content = json.dumps(content, ensure_ascii=False)
        out.append({"role": role, "content": content})
    return out or [{"role": "user", "content": fallback_prompt}]


def prepare_item(item_data: Dict[str, Any]) -> PreparedItem:
    handler = _WORKER_HANDLER
    tokenizer = _WORKER_TOKENIZER
    argsd = _WORKER_ARGS

    item = item_data.copy()
    item["formal_statement"] = replace_final_by_suffix(item["formal_statement"], ":= by sorry")

    if int(argsd["correction_round"]) > 0:
        error_str = get_error_str(
            item.get("compiled_code_that_failed_in_prev_round", ""),
            item.get("errors_for_compiled_code_from_prev_round", {}),
            argsd["error_thres"],
        )
        prompt, messages_history = handler.generate_correction_prompt(
            lean4_code_original_stmt=item["formal_statement"],
            history_messages_from_prev_round=item.get("history_messages_from_prev_round_for_new_prompt", []),
            prev_round_llm_raw_output=item.get("prev_round_llm_raw_output_for_new_prompt", ""),
            error_message_for_prev_round=error_str,
            tokenizer=tokenizer,
            current_correction_round_num=int(argsd["correction_round"]),
            unsolved_goals_restart_hint=item.get("unsolved_goals_restart_hint", False),
        )
    else:
        prompt, messages_history = handler.prover_inference(item["formal_statement"], tokenizer)

    token_nums = len(tokenizer.tokenize(prompt))
    return PreparedItem(
        item=item,
        prompt=prompt,
        messages_history=messages_history,
        api_messages=_sanitize_messages(messages_history, prompt),
        token_nums=token_nums,
    )


def _get_nested_int(data: Any, path: Sequence[str]) -> Optional[int]:
    cur = data
    for key in path:
        if not isinstance(cur, dict):
            return None
        cur = cur.get(key)
    if isinstance(cur, bool):
        return None
    if isinstance(cur, (int, float)):
        return int(cur)
    return None


def extract_token_stats(usage: Any) -> Dict[str, int]:
    if not isinstance(usage, dict):
        usage = {}

    input_tokens = (
        _get_nested_int(usage, ("input_tokens",))
        or _get_nested_int(usage, ("prompt_tokens",))
        or 0
    )
    output_tokens = (
        _get_nested_int(usage, ("output_tokens",))
        or _get_nested_int(usage, ("completion_tokens",))
        or 0
    )
    total_tokens = _get_nested_int(usage, ("total_tokens",)) or input_tokens + output_tokens


    return {
        "input_tokens": int(input_tokens),
        "output_tokens": int(output_tokens),
        "total_tokens": int(total_tokens),
    }


def _openai_headers(api_key: str) -> Dict[str, str]:
    return {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
    }


def _openrouter_headers(api_key: str) -> Dict[str, str]:
    headers = _openai_headers(api_key)
    referer = os.getenv("OPENROUTER_HTTP_REFERER") or os.getenv("OPENROUTER_SITE_URL")
    title = os.getenv("OPENROUTER_X_TITLE") or "ECP"
    if referer:
        headers["HTTP-Referer"] = referer
    if title:
        headers["X-Title"] = title
    return headers


def _raise_for_bad_response(resp: requests.Response) -> None:
    if 200 <= resp.status_code < 300:
        return
    body = resp.text
    if len(body) > 5000:
        body = body[:5000] + "\n...[truncated]"
    raise RuntimeError(f"HTTP {resp.status_code}: {body}")


def _extract_responses_text(data: Dict[str, Any]) -> str:
    text = data.get("output_text")
    if isinstance(text, str):
        return text

    chunks: List[str] = []
    for item in data.get("output") or []:
        if not isinstance(item, dict):
            continue
        for content in item.get("content") or []:
            if not isinstance(content, dict):
                continue
            value = content.get("text")
            if isinstance(value, str):
                chunks.append(value)
    return "".join(chunks)


def _call_openai_responses(messages: List[Dict[str, str]], argsd: Dict[str, Any]) -> Dict[str, Any]:
    api_key = argsd.get("openai_api_key") or os.getenv("OPENAI_API_KEY", "")
    if not api_key:
        raise RuntimeError("OPENAI_API_KEY is required for OpenAI-hosted gpt-5* prover models.")

    payload: Dict[str, Any] = {
        "model": argsd["model_path"],
        "input": messages,
        "temperature": float(argsd["temp"]),
        "max_output_tokens": int(argsd["api_max_output_tokens"]),
    }

    resp = requests.post(
        OPENAI_RESPONSES_URL,
        headers=_openai_headers(api_key),
        json=payload,
        timeout=float(argsd["request_timeout_s"]),
    )
    _raise_for_bad_response(resp)
    data = resp.json()
    usage = data.get("usage") or {}
    return {
        "text": _extract_responses_text(data),
        "usage": usage,
        "token_stats": extract_token_stats(usage),
        "response_meta": {
            "id": data.get("id"),
            "model": data.get("model"),
            "backend": "openai",
        },
    }


def _call_openrouter_chat(messages: List[Dict[str, str]], argsd: Dict[str, Any]) -> Dict[str, Any]:
    api_key = argsd.get("openrouter_api_key") or os.getenv("OPENROUTER_API_KEY", "")
    if not api_key:
        raise RuntimeError(
            "OPENROUTER_API_KEY is required for OpenRouter provider-prefixed prover models."
        )

    payload: Dict[str, Any] = {
        "model": argsd["model_path"],
        "messages": messages,
        "temperature": float(argsd["temp"]),
        "max_completion_tokens": int(argsd["api_max_output_tokens"]),
    }

    resp = requests.post(
        OPENROUTER_CHAT_COMPLETIONS_URL,
        headers=_openrouter_headers(api_key),
        json=payload,
        timeout=float(argsd["request_timeout_s"]),
    )
    _raise_for_bad_response(resp)
    data = resp.json()
    usage = data.get("usage") or {}
    try:
        text = data["choices"][0]["message"].get("content") or ""
    except Exception:
        text = json.dumps(data, ensure_ascii=False)[:20000]
    return {
        "text": text,
        "usage": usage,
        "token_stats": extract_token_stats(usage),
        "response_meta": {
            "id": data.get("id"),
            "model": data.get("model"),
            "provider": data.get("provider"),
            "backend": "openrouter",
        },
    }


def call_commercial_model(messages: List[Dict[str, str]], argsd: Dict[str, Any]) -> Dict[str, Any]:
    if argsd["backend"] == "openai":
        return _call_openai_responses(messages, argsd)
    if argsd["backend"] == "openrouter":
        return _call_openrouter_chat(messages, argsd)
    raise RuntimeError(f"Unknown backend: {argsd['backend']}")


def _code_record_from_item(item: Dict[str, Any]) -> Dict[str, Any]:
    return {
        "problem_id": item["problem_id"],
        "origin_problem_id": item.get("origin_problem_id"),
        "id_maps": item.get("id_maps"),
        "formal_statement": item.get("formal_statement", ""),
        "model_input": item.get("model_input", ""),
        "messages_history_list": item.get("messages_history_for_this_attempt"),
        "model_output": item.get("model_output", ""),
        "api_backend": item.get("api_backend"),
        "api_response_meta": item.get("api_response_meta", {}),
        "api_input_tokens": item.get("api_input_tokens", 0),
        "api_output_tokens": item.get("api_output_tokens", 0),
        "api_total_tokens": item.get("api_total_tokens", 0),
        "api_latency_s": item.get("api_latency_s", 0.0),
        "api_attempts": item.get("api_attempts", 0),
        "inference_error": item.get("inference_error", ""),
        "full_code": item.get("full_code", "None"),
    }


def finalize_generation(
    prepared: PreparedItem,
    call_result: Dict[str, Any],
    attempts: int,
    latency_s: float,
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    handler = _WORKER_HANDLER
    item = prepared.item.copy()
    for key in API_USAGE_METADATA_KEYS:
        item.pop(key, None)
    text = str(call_result.get("text") or "")
    token_stats = call_result.get("token_stats") or {}

    item["model_input"] = prepared.prompt
    item["messages_history_for_this_attempt"] = prepared.messages_history
    item["model_output"] = text
    item["api_backend"] = _WORKER_ARGS["backend"]
    item["api_response_meta"] = call_result.get("response_meta") or {}
    item["api_input_tokens"] = int(token_stats.get("input_tokens", 0))
    item["api_output_tokens"] = int(token_stats.get("output_tokens", 0))
    item["api_total_tokens"] = int(token_stats.get("total_tokens", 0))
    item["api_latency_s"] = float(latency_s)
    item["api_attempts"] = int(attempts)
    item["token_nums"] = prepared.token_nums

    extracted = handler.extrac_code(text)
    if extracted in ("None", None):
        item["full_code"] = "None"
    else:
        item["full_code"] = handler.problem_check(item["formal_statement"], extracted)

    return item, _code_record_from_item(item)


def finalize_error(
    item_data: Dict[str, Any],
    error: str,
    attempts: int,
    prepared: Optional[PreparedItem] = None,
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    item = prepared.item.copy() if prepared is not None else item_data.copy()
    for key in API_USAGE_METADATA_KEYS:
        item.pop(key, None)
    item.setdefault("formal_statement", item_data.get("formal_statement", ""))
    item["model_input"] = prepared.prompt if prepared is not None else ""
    item["messages_history_for_this_attempt"] = prepared.messages_history if prepared is not None else []
    item["model_output"] = ""
    item["api_backend"] = _WORKER_ARGS.get("backend", "")
    item["api_response_meta"] = {}
    item["api_input_tokens"] = 0
    item["api_output_tokens"] = 0
    item["api_total_tokens"] = 0
    item["api_latency_s"] = 0.0
    item["api_attempts"] = int(attempts)
    item["inference_error"] = error
    item["token_nums"] = prepared.token_nums if prepared is not None else 0
    item["full_code"] = "None"
    return item, _code_record_from_item(item)


def run_item_with_retries(item_data: Dict[str, Any]) -> Dict[str, Any]:
    prepared: Optional[PreparedItem] = None
    attempts = max(1, int(_WORKER_ARGS["retry"]))
    last_error = ""
    try:
        prepared = prepare_item(item_data)
    except Exception as exc:
        record, code = finalize_error(
            item_data,
            error=f"prompt_preparation_failed: {type(exc).__name__}: {exc}",
            attempts=0,
            prepared=None,
        )
        return {"problem_id": item_data.get("problem_id"), "record": record, "code": code, "ok": False}

    start_all = time.perf_counter()
    for attempt in range(1, attempts + 1):
        try:
            call_result = call_commercial_model(prepared.api_messages, _WORKER_ARGS)
            record, code = finalize_generation(
                prepared=prepared,
                call_result=call_result,
                attempts=attempt,
                latency_s=time.perf_counter() - start_all,
            )
            return {
                "problem_id": item_data.get("problem_id"),
                "record": record,
                "code": code,
                "ok": True,
            }
        except Exception as exc:
            last_error = f"{type(exc).__name__}: {exc}"
            if attempt < attempts:
                delay = min(30.0, 1.5 * (2 ** (attempt - 1))) + random.random()
                time.sleep(delay)

    record, code = finalize_error(
        item_data,
        error=last_error or "commercial model request failed",
        attempts=attempts,
        prepared=prepared,
    )
    return {"problem_id": item_data.get("problem_id"), "record": record, "code": code, "ok": False}


def init_worker(argsd: Dict[str, Any]) -> None:
    global _WORKER_ARGS, _WORKER_HANDLER, _WORKER_TOKENIZER
    _WORKER_ARGS = argsd
    _WORKER_HANDLER = build_handler(argsd["inference_handler"])
    _WORKER_TOKENIZER = CommercialPromptTokenizer()
    os.environ["PYTHONUNBUFFERED"] = "1"


def build_items(args: argparse.Namespace, handler: Any) -> List[Dict[str, Any]]:
    if args.correction_round > 0:
        prev_dir = args.previous_run_output_dir or args.output_dir
        if not prev_dir:
            raise ValueError("--previous_run_output_dir is required for correction_round>0")
        return load_data_for_correction(
            prev_dir,
            args.correction_round,
            args.n,
            args.base_output_template,
        )

    if not args.input_path:
        raise ValueError("--input_path is required for correction_round=0")
    initial = handler.load_split(args.input_path, args.split)

    items: List[Dict[str, Any]] = []
    for idata_orig in initial:
        origin_id = idata_orig.get("origin_problem_id", idata_orig.get("problem_id", idata_orig.get("name")))
        if not idata_orig.get("formal_statement"):
            continue
        for sample_idx in range(args.n):
            item = idata_orig.copy()
            item["origin_problem_id"] = origin_id
            item["problem_id"] = f"{origin_id}_g{sample_idx}"
            item["id_maps"] = [{"origin_problem_id": origin_id}, {"generation_id": item["problem_id"]}]
            items.append(item)
    return items


def usage_summary(records: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    def _sum(field: str) -> int:
        total = 0
        for row in records:
            try:
                total += int(row.get(field, 0) or 0)
            except Exception:
                pass
        return total

    api_errors = sum(1 for row in records if row.get("inference_error"))
    return {
        "records": len(records),
        "api_errors": int(api_errors),
        "api_calls": _sum("api_attempts"),
        "input_tokens": _sum("api_input_tokens"),
        "output_tokens": _sum("api_output_tokens"),
        "total_tokens": _sum("api_total_tokens"),
        "note": "output_tokens includes visible completion tokens plus invisible reasoning tokens when the backend reports them that way.",
    }


def save_outputs(
    output_dir: str,
    records_suffix: str,
    records: Sequence[Dict[str, Any]],
    codes: Sequence[Dict[str, Any]],
    write_checkpoint: bool = False,
    checkpoint_tag: str = "latest",
) -> None:
    records_list = dedup_by_key((strip_api_usage_metadata(row) for row in records), "problem_id")
    codes_list = dedup_by_key((strip_api_usage_metadata(row) for row in codes), "problem_id")

    safe_write_json(os.path.join(output_dir, f"full_records{records_suffix}.json"), records_list)
    safe_write_json(os.path.join(output_dir, f"to_inference_codes{records_suffix}.json"), codes_list)
    safe_write_json(
        os.path.join(output_dir, f"commercial_usage_summary{records_suffix}.json"),
        usage_summary(records_list),
    )

    if write_checkpoint:
        ckpt_dir = os.path.join(output_dir, "checkpoints")
        os.makedirs(ckpt_dir, exist_ok=True)
        safe_write_json(
            os.path.join(ckpt_dir, f"commercial_{checkpoint_tag}_records{records_suffix}.json"),
            records_list,
        )
        safe_write_json(
            os.path.join(ckpt_dir, f"commercial_{checkpoint_tag}_codes{records_suffix}.json"),
            codes_list,
        )


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input_path", default="", type=str)
    parser.add_argument("--model_path", required=True, type=str)
    parser.add_argument("--output_dir", required=True, type=str)
    parser.add_argument("--split", default="none", type=str)
    parser.add_argument("--n", default=1, type=int)
    parser.add_argument("--max_model_len", default=DEFAULT_MAX_MODEL_LEN, type=int)
    parser.add_argument(
        "--inference_handler",
        type=str,
        choices=["dpskcot", "dpsknoncot", "kiminacot"],
        required=True,
    )
    parser.add_argument("--trunck", default=1, type=int, help="Kept for CLI compatibility; unused.")
    parser.add_argument("--gpu", default=0, type=int, help="Ignored for commercial inference.")
    parser.add_argument("--node", default=1, type=int, help="Ignored; commercial inference is single-node.")
    parser.add_argument("--error_thres", default=True)
    parser.add_argument("--temp", default=1.0, type=float)
    parser.add_argument("--base_output_template", default="qwen", type=str)
    parser.add_argument("--correction_round", type=int, default=0)
    parser.add_argument("--previous_run_output_dir", type=str, default="")

    parser.add_argument("--parallel", type=int, default=DEFAULT_PARALLEL)
    parser.add_argument("--retry", type=int, default=3, help="Total API attempts per item.")
    parser.add_argument("--request_timeout_s", type=float, default=600.0)
    parser.add_argument(
        "--api_max_output_tokens",
        type=int,
        default=0,
        help="0 infers max_model_len - 5000; otherwise use this exact API output-token cap.",
    )
    parser.add_argument("--openai_api_key", default=os.getenv("OPENAI_API_KEY", ""), type=str)
    parser.add_argument("--openrouter_api_key", default=os.getenv("OPENROUTER_API_KEY", ""), type=str)
    parser.add_argument("--checkpoint_interval", type=int, default=8)
    parser.add_argument("--checkpoint_milestone", type=int, default=0)
    parser.add_argument("--debug_io", action="store_true")
    return parser


def args_to_dict(args: argparse.Namespace) -> Dict[str, Any]:
    max_output = args.api_max_output_tokens
    if max_output <= 0:
        max_output = infer_max_output_tokens(args.max_model_len)
    return {
        "model_path": args.model_path,
        "backend": infer_backend(args.model_path),
        "output_dir": args.output_dir,
        "split": args.split,
        "n": int(args.n),
        "max_model_len": int(args.max_model_len),
        "api_max_output_tokens": int(max_output),
        "temp": float(args.temp),
        "inference_handler": args.inference_handler,
        "correction_round": int(args.correction_round),
        "previous_run_output_dir": args.previous_run_output_dir,
        "base_output_template": args.base_output_template,
        "error_thres": args.error_thres,
        "parallel": int(args.parallel),
        "retry": int(args.retry),
        "request_timeout_s": float(args.request_timeout_s),
        "openai_api_key": args.openai_api_key,
        "openrouter_api_key": args.openrouter_api_key,
        "debug_io": bool(args.debug_io),
    }


def run_serial(items: Sequence[Dict[str, Any]], argsd: Dict[str, Any]) -> Iterable[Dict[str, Any]]:
    init_worker(argsd)
    for item in items:
        yield run_item_with_retries(item)


def main() -> None:
    os.environ["PYTHONUNBUFFERED"] = "1"
    args = build_arg_parser().parse_args()
    argsd = args_to_dict(args)

    if argsd["backend"] == "openai" and not argsd["openai_api_key"]:
        raise RuntimeError("OPENAI_API_KEY is required for OpenAI-hosted gpt-5* prover models.")
    if argsd["backend"] == "openrouter" and not argsd["openrouter_api_key"]:
        raise RuntimeError("OPENROUTER_API_KEY is required for OpenRouter prover models.")

    os.makedirs(args.output_dir, exist_ok=True)
    records_suffix = f"_corr{args.correction_round}" if args.correction_round > 0 else ""

    existing_records, existing_codes, completed_ids = load_existing_outputs(args.output_dir, records_suffix)
    if existing_records or existing_codes:
        save_outputs(args.output_dir, records_suffix, existing_records, existing_codes)

    handler = build_handler(args.inference_handler)
    items = build_items(args, handler)
    if completed_ids:
        before = len(items)
        items = [item for item in items if str(item.get("problem_id")) not in completed_ids]
        eprint(f"[RESUME] skipped {before - len(items)} completed; remaining {len(items)}")

    if not items:
        eprint("[Driver] nothing left to run; writing existing outputs and exit.")
        save_outputs(args.output_dir, records_suffix, existing_records, existing_codes)
        return

    eprint(
        f"[Driver] commercial backend={argsd['backend']} model={args.model_path}; "
        f"items={len(items)} parallel={args.parallel} retry={args.retry} "
        f"max_output_tokens={argsd['api_max_output_tokens']}"
    )

    records_by_id: Dict[str, Dict[str, Any]] = {str(r["problem_id"]): r for r in existing_records if r.get("problem_id")}
    codes_by_id: Dict[str, Dict[str, Any]] = {str(c["problem_id"]): c for c in existing_codes if c.get("problem_id")}
    completed_this_run = 0
    last_checkpoint_done = -1
    milestones: set[int] = set()

    def maybe_checkpoint(force: bool = False) -> None:
        nonlocal last_checkpoint_done
        interval = max(1, int(args.checkpoint_interval))
        if force or completed_this_run - last_checkpoint_done >= interval:
            save_outputs(
                args.output_dir,
                records_suffix,
                list(records_by_id.values()),
                list(codes_by_id.values()),
                write_checkpoint=True,
                checkpoint_tag="latest",
            )
            last_checkpoint_done = completed_this_run
            eprint(f"[CKPT] latest @done={completed_this_run}")

        milestone = int(args.checkpoint_milestone)
        if milestone > 0 and completed_this_run > 0 and completed_this_run % milestone == 0:
            if completed_this_run not in milestones:
                save_outputs(
                    args.output_dir,
                    records_suffix,
                    list(records_by_id.values()),
                    list(codes_by_id.values()),
                    write_checkpoint=True,
                    checkpoint_tag=f"done{completed_this_run}",
                )
                milestones.add(completed_this_run)
                eprint(f"[CKPT] milestone done{completed_this_run}")

    iterator: Iterable[Dict[str, Any]]
    pbar = tqdm(total=len(items), desc=f"Commercial progress (round {args.correction_round})")
    try:
        if int(args.parallel) <= 1:
            iterator = run_serial(items, argsd)
            for result in iterator:
                record = result["record"]
                code = result["code"]
                records_by_id[str(record["problem_id"])] = record
                codes_by_id[str(code["problem_id"])] = code
                completed_this_run += 1
                pbar.update(1)
                if args.debug_io and not result.get("ok", False):
                    eprint(f"[ERROR] {result.get('problem_id')}: {record.get('inference_error')}")
                maybe_checkpoint()
        else:
            ctx = mp.get_context("spawn")
            with ctx.Pool(
                processes=max(1, int(args.parallel)),
                initializer=init_worker,
                initargs=(argsd,),
                maxtasksperchild=32,
            ) as pool:
                for result in pool.imap_unordered(run_item_with_retries, items, chunksize=1):
                    record = result["record"]
                    code = result["code"]
                    records_by_id[str(record["problem_id"])] = record
                    codes_by_id[str(code["problem_id"])] = code
                    completed_this_run += 1
                    pbar.update(1)
                    if args.debug_io and not result.get("ok", False):
                        eprint(f"[ERROR] {result.get('problem_id')}: {record.get('inference_error')}")
                    maybe_checkpoint()
    finally:
        pbar.close()

    maybe_checkpoint(force=True)
    summary_path = os.path.join(args.output_dir, f"commercial_usage_summary{records_suffix}.json")
    eprint(f"[Driver] done. outputs:\n  {args.output_dir}/full_records{records_suffix}.json")
    eprint(f"[Driver] usage summary: {summary_path}")


if __name__ == "__main__":
    main()
