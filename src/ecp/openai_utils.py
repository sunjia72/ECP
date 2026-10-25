from __future__ import annotations

import ast  # for expression detection
import json
import os
import re
import subprocess
import textwrap
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union

import requests
import yaml
from openai import BadRequestError, OpenAI
from openai import DefaultHttpxClient
import httpx

# ---------------------------------------------------------------------
# Default OpenAI client (for OpenAI-hosted gpt-5 models)
# ---------------------------------------------------------------------
# Long timeouts: allow the model to think + tool loops to finish
_HTTP_TIMEOUT = httpx.Timeout(
    connect=30.0,   # connection setup
    read=600.0,     # server response streaming / long generation
    write=600.0,    # uploading large payloads
    pool=30.0,
)
_DEFAULT_TEMPERATURE = 0.0
_INVALID_PROMPT_MAX_RETRIES = 3
_INVALID_PROMPT_RETRY_BASE_DELAY_S = 1.0

client = OpenAI(
    timeout=600,
    max_retries=8,
    http_client=DefaultHttpxClient(timeout=_HTTP_TIMEOUT),
)


def _is_invalid_prompt_error(exc: BadRequestError) -> bool:
    """Return True for OpenAI 400s caused by prompt policy filtering."""
    parts: List[str] = [str(exc)]
    for attr in ("code", "message", "type"):
        value = getattr(exc, attr, None)
        if value:
            parts.append(str(value))

    body = getattr(exc, "body", None)
    if isinstance(body, dict):
        error_body = body.get("error")
        if isinstance(error_body, dict):
            for key in ("code", "message", "type", "param"):
                value = error_body.get(key)
                if value:
                    parts.append(str(value))
        else:
            parts.append(str(body))

    text = " ".join(parts).lower()
    return "invalid_prompt" in text or "invalid prompt" in text


def _create_with_invalid_prompt_retries(
    create_fn: Any,
    request_label: str,
    **kwargs: Any,
) -> Tuple[Any, int]:
    """
    Retry OpenAI invalid_prompt 400s.

    The OpenAI SDK retries transient transport/server failures, but 400s are not
    retried. These policy false positives have shown up intermittently on formal
    math prompts, so retry only this narrow BadRequestError class.
    """
    attempts = 0
    max_attempts = 1 + max(0, _INVALID_PROMPT_MAX_RETRIES)
    while True:
        attempts += 1
        try:
            return create_fn(**kwargs), attempts
        except BadRequestError as exc:
            if not _is_invalid_prompt_error(exc) or attempts >= max_attempts:
                raise
            delay_s = _INVALID_PROMPT_RETRY_BASE_DELAY_S * (2 ** (attempts - 1))
            print(
                f"[openai_utils] {request_label} got invalid_prompt 400; "
                f"retrying {attempts}/{_INVALID_PROMPT_MAX_RETRIES} after {delay_s:.1f}s"
            )
            time.sleep(delay_s)


# ---------------------------------------------------------------------
# Helpers for cleaning / massaging model-generated code
# ---------------------------------------------------------------------
def _remove_fences(code: str) -> str:
    """
    Remove all triple-backtick code fences and language tags like ```python, ```py, ``` etc.
    Works even if closing fence is missing.
    """
    if not isinstance(code, str):
        return code
    code = re.sub(r"```[ \t]*[A-Za-z0-9_+-]*", "", code)
    code = code.replace("```", "")
    return code.strip()


def _maybe_wrap_print(code: str) -> str:
    """
    If the last line is a (syntactically valid) Python expression, wrap it with print(...).
    Handles e.g.:
        results[:10], results[10:20], results[20:30]
    while leaving real statements (def/for/if/...) untouched.
    """
    code = _remove_fences(code)
    lines = code.rstrip().splitlines()
    if not lines:
        return code

    last = lines[-1].strip()
    if not last:
        return code

    if (
        re.match(
            r"^(def|class|for|if|while|with|return|import|from|try|except|finally|async|await|global|nonlocal|raise|assert|pass|break|continue)\b",
            last,
        )
        or last.endswith(":")
        or re.match(r"^\s*print\s*\(", last)
    ):
        return code

    try:
        ast.parse(last, mode="eval")
        lines[-1] = f"print({last})"
        return "\n".join(lines)
    except SyntaxError:
        return code


# ---------------------------------------------------------------------
# Load localhost.yaml config (always from configs/localhost.yaml)
# ---------------------------------------------------------------------
def _localhost_yaml_path() -> Optional[Path]:
    project = os.getenv("PROJECT")
    if not project:
        return None
    return Path("configs") / "localhost.yaml"


def _load_localhost_config() -> dict:
    """

    Expected structure like:
      informal_llm:
        base_url: http://172.26.93.141:30000/v1
      sandbox_fusion:
        base_url: http://172.26.93.103:10080/run_code
    """
    p = _localhost_yaml_path()
    if p is None or not p.exists():
        return {}

    try:
        with open(p, "r") as f:
            cfg = yaml.safe_load(f) or {}
        return cfg if isinstance(cfg, dict) else {}
    except Exception:
        return {}


def _get_informal_llm_base_url(cfg: dict) -> str:
    return str((((cfg or {}).get("informal_llm") or {}).get("base_url") or "")).strip()


def _get_sandbox_fusion_base_url(cfg: dict) -> str:
    return str((((cfg or {}).get("sandbox_fusion") or {}).get("base_url") or "")).strip()


def _probe_url(url: str, timeout_s: float = 1.0) -> bool:
    """
    "Ping" a URL to see if it's reachable.

    We intentionally accept non-2xx responses (e.g. 404/405) as "reachable",
    since /run_code endpoints often don't implement GET.
    """
    if not url:
        return False
    try:
        resp = requests.get(url, timeout=timeout_s)
        return resp is not None
    except Exception:
        return False


# ---------------------------------------------------------------------
# Local Python executor (fallback when Sandbox Fusion not reachable)
# ---------------------------------------------------------------------
def _run_python_local(code: str) -> str:
    """
    Local 'code_exec' implementation using a Python subprocess.
    VERY DANGEROUS in production – sandbox it if you care about security.
    """
    code = textwrap.dedent(code)

    proc = subprocess.Popen(
        ["python3", "-u", "-"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    try:
        out, _ = proc.communicate(code, timeout=60)
    except subprocess.TimeoutExpired:
        proc.kill()
        out, _ = proc.communicate()
        out = (out or "") + "\n[LocalExecutor] Timed out after 60 seconds."

    if len(out) > 5000:
        return out[:5000] + "\n[LocalExecutor] Output too long. Truncated."
    return out


# ---------------------------------------------------------------------
# Sandbox Fusion-backed Python executor (remote)
# ---------------------------------------------------------------------
def _run_python_remote(code: str, sandbox_fusion_base_url: str) -> str:
    """
    'code_exec' tool implementation backed by Sandbox Fusion.
    Sends code to the remote Sandbox Fusion /run_code endpoint and returns
    the textual result for the LLM.
    """
    code = textwrap.dedent(code)

    compile_timeout = 60
    run_timeout = 60
    memory_limit_mb = 1024

    payload = {
        "compile_timeout": compile_timeout,
        "run_timeout": run_timeout,
        "code": code,
        "language": "python",
        "memory_limit_MB": memory_limit_mb,
    }

    request_timeout = compile_timeout + run_timeout + 10

    try:
        resp = requests.post(
            sandbox_fusion_base_url,
            json=payload,
            timeout=request_timeout,
        )
        resp.raise_for_status()
    except Exception as e:
        return f"[SandboxFusionError] HTTP error: {repr(e)}"

    try:
        data = resp.json()
    except Exception:
        return resp.text

    # Prefer stdout/stderr if present; otherwise dump JSON
    run_result = data.get("run_result") or {}
    if isinstance(run_result, dict) and run_result:
        stdout = run_result.get("stdout", "") or ""
        stderr = run_result.get("stderr", "") or ""
        final_output = stdout + stderr
        if len(final_output) > 5000:
            return f"{final_output}\n[SandboxFusion] Output too long. Truncated."
        return final_output

    return "[SandboxFusionError] No run_result in response. Please rewrite the code."


# ---------------------------------------------------------------------
# Unified Python executor:
#   - Always load sandbox_fusion.base_url from localhost.yaml
#   - Probe it; if reachable use it; else fall back to local
# ---------------------------------------------------------------------
def run_python(code: str) -> str:
    """
    Wrapper that picks Sandbox Fusion if reachable, otherwise local subprocess.
    """
    cfg = _load_localhost_config()
    sandbox_fusion_base_url = _get_sandbox_fusion_base_url(cfg)

    if sandbox_fusion_base_url and _probe_url(sandbox_fusion_base_url):
        return _run_python_remote(code, sandbox_fusion_base_url=sandbox_fusion_base_url)

    return _run_python_local(code)


# ---------------------------------------------------------------------
# Client factory: choose OpenAI/OpenRouter/local endpoint based on model name
# ---------------------------------------------------------------------
def _mk_client(
    *,
    api_key: Optional[str] = None,
    base_url: Optional[str] = None,
    default_headers: Optional[Dict[str, str]] = None,
) -> OpenAI:
    kwargs = {
        "timeout": _HTTP_TIMEOUT,
        "max_retries": 8,
        "http_client": DefaultHttpxClient(timeout=_HTTP_TIMEOUT),
    }
    if api_key:
        kwargs["api_key"] = api_key
    if base_url:
        kwargs["base_url"] = base_url
    if default_headers:
        kwargs["default_headers"] = default_headers
    return OpenAI(**kwargs)


def _is_openai_hosted_model(model: str) -> bool:
    """
    Return True for OpenAI-hosted GPT-5 family models.
    Examples: gpt-5, gpt-5.4, gpt-5.4, gpt-5.4-mini.
    """
    m = (model or "").strip().lower()
    return m.startswith("gpt-5")


def _is_openrouter_model(model: str) -> bool:
    """Route provider-prefixed models through OpenRouter."""
    m = (model or "").lower()
    return "openai/" in m or "google/" in m


def _get_openrouter_client() -> OpenAI:
    api_key = os.getenv("OPENROUTER_API_KEY")
    if not api_key:
        raise RuntimeError(
            "OPENROUTER_API_KEY is required for OpenRouter models "
            "(model names containing 'openai/' or 'google/')."
        )

    headers: Dict[str, str] = {}
    referer = os.getenv("OPENROUTER_HTTP_REFERER") or os.getenv("OPENROUTER_SITE_URL")
    title = os.getenv("OPENROUTER_X_TITLE") or "ECP"
    if referer:
        headers["HTTP-Referer"] = referer
    if title:
        headers["X-Title"] = title

    return _mk_client(
        api_key=api_key,
        base_url="https://openrouter.ai/api/v1",
        default_headers=headers or None,
    )


def _get_client_for_model(model: str) -> OpenAI:
    if _is_openrouter_model(model):
        return _get_openrouter_client()

    if _is_openai_hosted_model(model):
        return client

    cfg = _load_localhost_config()
    informal_llm_base_url = _get_informal_llm_base_url(cfg)
    if informal_llm_base_url:
        return _mk_client(base_url=informal_llm_base_url)

    return client



# ---------------------------------------------------------------------
# NEW: Decide whether to use Responses API or Chat Completions API
# ---------------------------------------------------------------------
def _should_use_chat_completions(model: str, llm_client: OpenAI) -> bool:
    """
    Many OpenAI-compatible local servers (e.g. vLLM) implement chat.completions tool-calling
    more reliably than Responses tool-calling.
    We keep OpenAI-hosted gpt-5* on Responses, and route everything else with a custom base_url
    to chat.completions.
    """
    if _is_openrouter_model(model):
        return True

    if _is_openai_hosted_model(model):
        return False

    base_url = getattr(llm_client, "base_url", None)
    base_url = str(base_url) if base_url is not None else ""

    # If a non-empty custom base_url is set, it's likely a local/compatible server
    return bool(base_url and base_url != "https://api.openai.com/v1")


def _extract_output_tokens(usage: Any) -> int:
    """
    Best-effort extraction of output/completion token count from OpenAI/compatible usage objects.
    """
    if usage is None:
        return 0

    try:
        if isinstance(usage, dict):
            if isinstance(usage.get("output_tokens"), int):
                return int(usage["output_tokens"])
            if isinstance(usage.get("completion_tokens"), int):
                return int(usage["completion_tokens"])
            out_details = usage.get("output_tokens_details")
            if isinstance(out_details, dict) and isinstance(out_details.get("total"), int):
                return int(out_details["total"])
            return 0

        output_tokens = getattr(usage, "output_tokens", None)
        if isinstance(output_tokens, int):
            return output_tokens

        completion_tokens = getattr(usage, "completion_tokens", None)
        if isinstance(completion_tokens, int):
            return completion_tokens

        out_details = getattr(usage, "output_tokens_details", None)
        if out_details is not None:
            total = getattr(out_details, "total", None)
            if isinstance(total, int):
                return total
            if isinstance(out_details, dict) and isinstance(out_details.get("total"), int):
                return int(out_details["total"])
    except Exception:
        return 0

    return 0


def _make_llm_stats(runtime_s: float, output_tokens: int, tool_calls: int, api_calls: int) -> Dict[str, Any]:
    return {
        "runtime_sec": float(runtime_s),
        "output_tokens": int(output_tokens),
        "tool_calls": int(tool_calls),
        "api_calls": int(api_calls),
    }


def _serialize_chat_tool_calls(tool_calls: Any) -> List[Dict[str, Any]]:
    """Convert SDK tool-call objects into OpenAI-compatible request dictionaries."""
    out: List[Dict[str, Any]] = []
    for tc in tool_calls or []:
        fn = getattr(tc, "function", None)
        out.append(
            {
                "id": getattr(tc, "id", ""),
                "type": getattr(tc, "type", "function"),
                "function": {
                    "name": getattr(fn, "name", ""),
                    "arguments": getattr(fn, "arguments", "") or "{}",
                },
            }
        )
    return out


# ---------------------------------------------------------------------
# OpenAI Responses-style multi-turn tool usage (function tools, NOT custom)
# ---------------------------------------------------------------------
def _call_openai_responses_llm(
    user_prompt: str, model: str
) -> Tuple[str, Dict[str, Any]]:
    """
    Uses Responses API with a FUNCTION tool called code_exec.
    This avoids 'type: custom' which many backends reject.
    """
    tools = [
    {
        "type": "function",
        "name": "code_exec",  # <-- REQUIRED by your endpoint
        "description": (
            "Executes arbitrary Python code. Uses Sandbox Fusion if reachable, "
            "otherwise falls back to a local Python subprocess."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "code": {"type": "string", "description": "Python code to execute."}
            },
            "required": ["code"],
        },
    }
]

    llm_client = _get_client_for_model(model)

    common_kwargs = {
        "model": model,
        "tools": tools,
        "temperature": _DEFAULT_TEMPERATURE,
    }

    start_t = time.perf_counter()
    total_output_tokens = 0
    total_tool_calls = 0
    api_calls = 0

    response, attempts = _create_with_invalid_prompt_retries(
        llm_client.responses.create,
        f"responses.create({model}, initial)",
        input=[{"role": "user", "content": user_prompt}],
        **common_kwargs,
    )
    api_calls += attempts
    total_output_tokens += _extract_output_tokens(getattr(response, "usage", None))

    MAX_TOOL_CALLS = 10
    tool_call_round = 0
    output = ""
    final_round_started = False

    while True:
        # Collect FUNCTION tool calls in Responses output
        tool_calls = []
        for item in getattr(response, "output", []) or []:
            if getattr(item, "type", None) in ("function_call", "tool_call"):
                tool_calls.append(item)


        if final_round_started or not tool_calls:
            break

        if tool_call_round >= MAX_TOOL_CALLS:
            output += (
                f"\n[TOOL LIMIT] Maximum tool-call rounds ({MAX_TOOL_CALLS}) reached. "
                "Ignoring further tool calls and finalizing answer."
            )
            break

        output += f"\n===== ENUMERATOR ROUND {tool_call_round + 1} ====="
        tool_call_round += 1
        tool_call_outputs: List[Dict[str, Any]] = []

        for item in tool_calls:
            total_tool_calls += 1
            call_id = getattr(item, "call_id", None)
            fn_name = getattr(item, "name", None)
            raw_args = getattr(item, "arguments", None) or "{}"

            if fn_name != "code_exec":
                result = f"[ToolError] Unknown tool '{fn_name}'. Expected 'code_exec'."
            else:
                try:
                    args = json.loads(raw_args) if isinstance(raw_args, str) else (raw_args or {})
                except Exception:
                    args = {"code": str(raw_args)}

                code = args.get("code", "")
                code = _remove_fences(code)
                code = _maybe_wrap_print(code)

                output += f"\n[TOOL CALL] {fn_name} (call_id={call_id}):\n{code}\n"
                result = run_python(code)
                output += "[TOOL OUTPUT]\n" + result

            tool_call_outputs.append(
                {
                    "type": "function_call_output",
                    "call_id": call_id,
                    "output": result,
                }
            )

        if tool_call_round < MAX_TOOL_CALLS:
            response, attempts = _create_with_invalid_prompt_retries(
                llm_client.responses.create,
                f"responses.create({model}, tool_round={tool_call_round})",
                input=tool_call_outputs,
                previous_response_id=response.id,
                model=model,
                tools=tools,
                temperature=_DEFAULT_TEMPERATURE,
            )
            api_calls += attempts
            total_output_tokens += _extract_output_tokens(getattr(response, "usage", None))
        else:
            final_round_started = True
            finalizing_input = list(tool_call_outputs) + [
                {
                    "role": "user",
                    "content": (
                        "You have now reached the maximum number of tool calls. "
                        "Do NOT call any tools anymore. "
                        "Using the tool outputs above, provide your final answer."
                    ),
                }
            ]

            response, attempts = _create_with_invalid_prompt_retries(
                llm_client.responses.create,
                f"responses.create({model}, finalizing)",
                input=finalizing_input,
                previous_response_id=response.id,
                model=model,
                temperature=_DEFAULT_TEMPERATURE,
            )
            api_calls += attempts
            total_output_tokens += _extract_output_tokens(getattr(response, "usage", None))

    # Extract final answer text
    final_text_chunks: List[str] = []
    for item in getattr(response, "output", []) or []:
        content = getattr(item, "content", None)
        if content:
            for c in content:
                t = getattr(c, "text", None)
                if t:
                    final_text_chunks.append(t)

    final_answer = "".join(final_text_chunks)
    output += "\n=== CONJECTURER ===\n" + final_answer
    stats = _make_llm_stats(
        runtime_s=time.perf_counter() - start_t,
        output_tokens=total_output_tokens,
        tool_calls=total_tool_calls,
        api_calls=api_calls,
    )
    return output, stats


# ---------------------------------------------------------------------
# Chat Completions multi-turn loop (function tools) for OpenAI-compatible servers
# ---------------------------------------------------------------------
def _call_openai_chat_llm_with_tools(
    user_prompt: str, model: str
) -> Tuple[str, Dict[str, Any]]:
    """
    Uses chat.completions with function tools (high compatibility with vLLM).
    """
    llm_client = _get_client_for_model(model)

    tools = [
        {
            "type": "function",
            "function": {
                "name": "code_exec",
                "description": (
                    "Executes arbitrary Python code. "
                    "Uses a remote Sandbox Fusion environment if reachable, "
                    "otherwise falls back to a local Python subprocess."
                ),
                "parameters": {
                    "type": "object",
                    "properties": {
                        "code": {
                            "type": "string",
                            "description": "Python code to execute. Do NOT wrap it in backticks.",
                        }
                    },
                    "required": ["code"],
                },
            },
        }
    ]

    messages: List[Dict[str, Any]] = [{"role": "user", "content": user_prompt}]
    output = ""
    MAX_TOOL_CALL_ROUNDS = 10
    tool_round = 0
    final_round_started = False
    start_t = time.perf_counter()
    total_output_tokens = 0
    total_tool_calls = 0
    api_calls = 0

    while True:
        allow_tools = (tool_round < MAX_TOOL_CALL_ROUNDS) and not final_round_started

        if allow_tools:
            resp, attempts = _create_with_invalid_prompt_retries(
                llm_client.chat.completions.create,
                f"chat.completions.create({model}, tools)",
                model=model,
                messages=messages,
                tools=tools,
                tool_choice="auto",
                temperature=_DEFAULT_TEMPERATURE,
            )
        else:
            resp, attempts = _create_with_invalid_prompt_retries(
                llm_client.chat.completions.create,
                f"chat.completions.create({model}, no_tools)",
                model=model,
                messages=messages,
                temperature=_DEFAULT_TEMPERATURE,
            )
        api_calls += attempts
        total_output_tokens += _extract_output_tokens(getattr(resp, "usage", None))

        msg = resp.choices[0].message

        # Append assistant message (preserving tool_calls if any)
        if getattr(msg, "tool_calls", None):
            messages.append(
                {
                    "role": "assistant",
                    "content": msg.content or "",
                    "tool_calls": _serialize_chat_tool_calls(msg.tool_calls),
                }
            )
        else:
            messages.append({"role": "assistant", "content": msg.content or ""})

        tool_calls = getattr(msg, "tool_calls", None) or []

        if not allow_tools or not tool_calls:
            output += "\n=== FINAL MODEL ANSWER ===\n" + (msg.content or "")
            stats = _make_llm_stats(
                runtime_s=time.perf_counter() - start_t,
                output_tokens=total_output_tokens,
                tool_calls=total_tool_calls,
                api_calls=api_calls,
            )
            return output, stats

        output += f"\n===== TOOL CALL ROUND {tool_round + 1} ====="
        tool_round += 1

        for tc in tool_calls:
            total_tool_calls += 1
            fn = tc.function
            fn_name = fn.name
            raw_args = fn.arguments or "{}"

            try:
                args = json.loads(raw_args) if raw_args else {}
            except Exception:
                args = {"code": raw_args}

            code = args.get("code", "")
            code = _remove_fences(code)
            code = _maybe_wrap_print(code)

            output += f"\n[TOOL CALL] {fn_name} (id={tc.id}):\n{code}\n"

            if fn_name != "code_exec":
                result = f"[ToolError] Unknown tool '{fn_name}'. Expected 'code_exec'. Raw args: {raw_args}"
            else:
                result = run_python(code)

            output += "[TOOL OUTPUT]\n" + result

            messages.append(
                {
                    "role": "tool",
                    "tool_call_id": tc.id,
                    "content": result,
                }
            )

        if tool_round >= MAX_TOOL_CALL_ROUNDS:
            final_round_started = True
            messages.append(
                {
                    "role": "user",
                    "content": (
                        "You have reached the maximum number of tool calls. "
                        "Do NOT call tools anymore. Using the tool outputs above, provide your final answer."
                    ),
                }
            )


# ---------------------------------------------------------------------
# Public entrypoint: works for OpenAI-hosted, OpenRouter, and local OpenAI-compatible models
# ---------------------------------------------------------------------
def call_llm(
    user_prompt: str,
    model: str = "gpt-5.4",
    allow_tools: bool = True,
    return_stats: bool = False,
) -> Union[str, Tuple[str, Dict[str, Any]]]:
    """
    High-level entrypoint:
      - OpenAI-hosted gpt-5/gpt-5.4: Responses API (with function tools if allow_tools=True).
      - OpenRouter models containing 'openai/' or 'google/': chat.completions endpoint.
      - Other models:
          - If configured with a custom base_url (likely vLLM): chat.completions tools loop
          - Else: Responses API
    """
    start_t = time.perf_counter()

    # --- OpenAI / other models path ---
    llm_client = _get_client_for_model(model)

    if allow_tools:
        # If this is a local/vLLM-like endpoint, use chat.completions (most compatible)
        if _should_use_chat_completions(model, llm_client):
            text, stats = _call_openai_chat_llm_with_tools(user_prompt, model=model)
            return (text, stats) if return_stats else text
        # Otherwise use Responses API with function tools
        text, stats = _call_openai_responses_llm(user_prompt, model=model)
        return (text, stats) if return_stats else text

    # allow_tools=False: pure text
    # Prefer Responses for OpenAI-hosted; for local servers, chat.completions is safer.
    if _should_use_chat_completions(model, llm_client):
        resp, attempts = _create_with_invalid_prompt_retries(
            llm_client.chat.completions.create,
            f"chat.completions.create({model}, text_only)",
            model=model,
            messages=[{"role": "user", "content": user_prompt}],
            temperature=_DEFAULT_TEMPERATURE,
        )
        text = resp.choices[0].message.content or ""
        stats = _make_llm_stats(
            runtime_s=time.perf_counter() - start_t,
            output_tokens=_extract_output_tokens(getattr(resp, "usage", None)),
            tool_calls=0,
            api_calls=attempts,
        )
        return (text, stats) if return_stats else text

    resp, attempts = _create_with_invalid_prompt_retries(
        llm_client.responses.create,
        f"responses.create({model}, text_only)",
        model=model,
        input=[{"role": "user", "content": user_prompt}],
        temperature=_DEFAULT_TEMPERATURE,
    )
    final_text_chunks: List[str] = []
    for item in getattr(resp, "output", []) or []:
        content = getattr(item, "content", None)
        if content:
            for c in content:
                t = getattr(c, "text", None)
                if t:
                    final_text_chunks.append(t)
    text = "".join(final_text_chunks)
    stats = _make_llm_stats(
        runtime_s=time.perf_counter() - start_t,
        output_tokens=_extract_output_tokens(getattr(resp, "usage", None)),
        tool_calls=0,
        api_calls=attempts,
    )
    return (text, stats) if return_stats else text


def call_llm_text_with_stats(
    prompt: str,
    model: str = "gpt-5.4",
    allow_tools: bool = True,
) -> Tuple[str, Dict[str, Any]]:
    """
    Return assistant text plus aggregated runtime/output-token/tool-call stats.
    """
    text, stats = call_llm(
        prompt,
        model=model,
        allow_tools=allow_tools,
        return_stats=True,
    )
    return str(text), stats


# ---------------------------------------------------------------------
# Example usage
# ---------------------------------------------------------------------
if __name__ == "__main__":
    # Example: swap model to your local model name if you want
    # model = "openai/gpt-oss-120b"
    model = "gpt-5.4"

    prompt = (
        "Write a short Python script that computes 2+2, run it using the code_exec tool, "
        "and then tell me the result."
    )
    print(call_llm(prompt, model=model, allow_tools=True))
