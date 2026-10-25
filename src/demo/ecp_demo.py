from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import sys
import time
from pathlib import Path
from typing import Any, Dict, Optional, Sequence, Tuple

import requests
import yaml

from src.ecp.main import (
    DEFAULT_PROVER_MAX_MODEL_LEN,
    build_prover_records,
    construct_answer_for_entry,
    load_successful_proof_bodies,
    read_final_summary,
    run_final_automation_fallback,
    run_proof_gen,
    write_jsonl,
)
from src.ecp.utils import (
    answer_substituted_theorem,
    assemble_existential_proof,
    ecp_preamble,
    extract_outer_exists_binder,
    extract_proof_body,
    formal_equivalence_checker,
    is_true_value,
    run_lean_code,
    run_lean_code_repl,
    run_lean_file,
    strip_theorem_proof_suffix,
    verify_answer_admissibility,
    verify_answer_syntax,
)
from src.goedel.utils import (
    DeepSeekCoTHandler,
    DeepSeekNonCoTHandler,
    KiminaCoTHandler,
    get_error_str,
    replace_final_by_suffix,
)


DEFAULT_HEADER = """import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0"""

QUANTIFIER_OPTION_KEY = "allow_quantifier"
QUANTIFIER_OPTION_DEFAULT = True

BASIC_VOCABULARY = ["OfNat.ofNat"]

ARITHMETIC_VOCABULARY = [
    "OfNat",
    "OfNat.ofNat",
    "OfScientific",
    "OfScientific.ofScientific",
    "NNRatCast.toOfScientific",
    "Nat.cast",
    "Int.cast",
    "Rat.cast",
    "Rat.instNatCast",
    "Nat.zero",
    "Nat.succ",
    "Nat.pred",
    "Bool.true",
    "Bool.false",
    "HAdd.hAdd",
    "HSub.hSub",
    "HMul.hMul",
    "HDiv.hDiv",
    "HPow.hPow",
    "Neg.neg",
    "Real.pi",
    "Real.exp",
    "Real.log",
]

ADVANCED_ARITHMETIC_VOCABULARY = sorted(
    set(
        ARITHMETIC_VOCABULARY
        + [
            "HMod.hMod",
            "abs",
            "Real.sqrt",
            "Nat.sqrt",
            "Int.sqrt",
            "Rat.sqrt",
            "Nat.add",
            "Nat.mul",
            "Nat.sub",
            "Nat.pow",
            "Nat.factorial",
            "Nat.choose",
            "Nat.fib",
            "Nat.gcd",
            "Nat.lcm",
            "Nat.mod",
            "Dvd.dvd",
            "Nat.ModEq",
            "Int.ModEq",
            "Nat.floor",
            "Int.floor",
            "Nat.ceil",
            "Int.ceil",
            "Int.ediv",
            "Int.emod",
            "Even",
            "Odd",
            "Prime",
            "Nat.Prime",
            "Real.sin",
            "Real.cos",
            "Real.tan",
            "Real.sinh",
            "Real.cosh",
            "Real.tanh",
            "Real.arctan",
            "Real.arccos",
            "Real.arcsin",
            "Rat.sqrt",
        ]
    )
)

ALL_DEMO_VOCABULARY = sorted(
    set(
        ADVANCED_ARITHMETIC_VOCABULARY
        + [
            "Eq",
            "And",
            "Or",
            "Iff",
            "Not",
            "Exists",
            "True",
            "False",
            "ite",
            "LT.lt",
            "LE.le",
            "GT.gt",
            "GE.ge",
            "EmptyCollection.emptyCollection",
            "Singleton.singleton",
            "Set.singleton",
            "Insert.insert",
            "Set.insert",
            "setOf",
            "Set.Mem",
            "Set.univ",
            "Union.union",
            "Inter.inter",
            "Set.Ici",
            "Set.Ioi",
            "Set.Iic",
            "Set.Iio",
            "Set.Icc",
            "Set.Ioo",
            "Set.Ioc",
            "Set.Ico",
            "Finset.card",
            "Finset.sum",
            "Finset.product",
            "Finset.range",
            "Finset.prod",
            "Finset.Subtype.fintype",
            "Finset.add",
            "Finset.Ici",
            "Finset.Ioi",
            "Finset.Iic",
            "Finset.Iio",
            "Finset.Icc",
            "Finset.Ioo",
            "Finset.Ioc",
            "Finset.Ico",
            "Prod.mk",
            "Prod.fst",
            "Prod.snd",
            "Subtype.mk",
            "Subtype.val",
            "Polynomial.X",
            "Polynomial.C",
            "Polynomial.eval",
            "Polynomial.map",
            "Polynomial.degree",
            "Polynomial.natDegree",
            "Polynomial.mul'",
            "Polynomial.add'",
            "Complex.mk",
            "Complex.ofReal",
            "Complex.I",
        ]
    )
)

LEVEL_VOCABULARIES = {
    "basic": BASIC_VOCABULARY,
    "arithmetic": ARITHMETIC_VOCABULARY,
    "advanced_arithmetic": ADVANCED_ARITHMETIC_VOCABULARY,
    "all": ALL_DEMO_VOCABULARY,
}

COMMERCIAL_PROVER_PREFIXES = (
    "gpt-5",
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


def parse_bool(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    text = str(value).strip().lower()
    if text in {"1", "true", "yes", "y", "on"}:
        return True
    if text in {"0", "false", "no", "n", "off"}:
        return False
    raise argparse.ArgumentTypeError(f"Expected a boolean value, got {value!r}.")


def _maybe_read_stdin() -> str:
    if sys.stdin is not None and not sys.stdin.isatty():
        return sys.stdin.read()
    return ""


def read_text_arg(
    *,
    direct: Optional[str] = None,
    path: Optional[str] = None,
    stdin_if_missing: bool = False,
) -> str:
    if direct:
        return direct
    if path:
        return Path(path).read_text(encoding="utf-8")
    if stdin_if_missing:
        return _maybe_read_stdin()
    return ""


def sanitize_file_stem(name: str) -> str:
    text = re.sub(r"[^A-Za-z0-9_.-]+", "_", str(name)).strip("._")
    return text or "demo"


def sanitize_lean_ident(name: str) -> str:
    text = re.sub(r"[^A-Za-z0-9_']+", "_", str(name)).strip("_")
    if not text:
        text = "demo"
    if text[0].isdigit():
        text = "n_" + text
    return text


def now_tag() -> str:
    return time.strftime("%Y%m%d_%H%M%S")


def normalize_theorem_part(theorem_text: str) -> str:
    theorem_text = theorem_text.strip()
    decl = strip_theorem_proof_suffix(theorem_text)
    return decl.rstrip() + " := by sorry"


def split_theorem_source(source: str) -> Tuple[str, str]:
    text = (source or "").strip()
    match = re.search(r"(^|\n)\s*theorem\s+", text)
    if not match:
        raise ValueError("Input must contain a Lean `theorem` declaration.")
    theorem_start = match.start()
    if text[theorem_start] == "\n":
        theorem_start += 1
    preamble = text[:theorem_start].strip()
    theorem = normalize_theorem_part(text[theorem_start:].strip())
    return preamble or DEFAULT_HEADER, theorem


def theorem_name(theorem_part_full: str) -> str:
    match = re.match(r"\s*theorem\s+([^\s:]+)", theorem_part_full)
    if not match:
        raise ValueError("Could not parse theorem name.")
    return match.group(1)


def _quote_name(name: str) -> str:
    value = name.strip()
    if not value:
        return ""
    if value.startswith("``"):
        return value
    if value.startswith("`"):
        value = value.lstrip("`")
    return "``" + value


def normalize_admissible_vocabulary(raw: Optional[str], level: str) -> str:
    if raw:
        text = raw.strip()
        if text.startswith("[") and text.endswith("]"):
            return text
        parts = [p.strip() for p in re.split(r"[,\s]+", text) if p.strip()]
        names = [_quote_name(part) for part in parts]
        return "[" + ", ".join(name for name in names if name) + "]"

    names = [_quote_name(name) for name in LEVEL_VOCABULARIES[level]]
    return "[" + ", ".join(names) + "]"


def structural_options_from_args(args: argparse.Namespace) -> Dict[str, bool]:
    value = getattr(args, QUANTIFIER_OPTION_KEY, None)
    if value is None:
        value = QUANTIFIER_OPTION_DEFAULT
    value = bool(value)
    setattr(args, QUANTIFIER_OPTION_KEY, value)
    return {QUANTIFIER_OPTION_KEY: value}


def admissibility_info_from_args(args: argparse.Namespace) -> Dict[str, Any]:
    info: Dict[str, Any] = {
        "level": args.level,
        "admissible_vocabulary": normalize_admissible_vocabulary(
            args.admissible_vocabulary,
            args.level,
        ),
    }
    info.update(structural_options_from_args(args))
    return info


def entry_from_theorem_source(source: str, args: argparse.Namespace) -> Dict[str, Any]:
    header, theorem_part_full = split_theorem_source(source)
    answer_name, answer_type, _ = extract_outer_exists_binder(theorem_part_full)
    name = args.problem_name or theorem_name(theorem_part_full)
    return {
        "name": name,
        "split": "demo",
        "is_formalized": "True",
        "header": header,
        "additional_info_after_answer": "",
        "theorem_part_full": theorem_part_full,
        "answer_name": answer_name,
        "answer_type": answer_type,
        "formal_answer": "",
        "formal_answer_info": admissibility_info_from_args(args),
    }


def answer_check_passed(result: Any) -> bool:
    if isinstance(result, dict):
        messages = result.get("messages")
        if isinstance(messages, list) and any(
            isinstance(msg, dict) and msg.get("severity") == "error"
            for msg in messages
        ):
            return False
    text = result if isinstance(result, str) else json.dumps(result, ensure_ascii=False)
    return (
        "error:" not in text
        and '"severity":"error"' not in text
        and '"severity": "error"' not in text
        and "'severity': 'error'" not in text
    )


class SimpleChatTemplateTokenizer:
    """Tiny facade for Goedel prompt handlers in demo HTTP mode."""

    def apply_chat_template(
        self,
        messages: Sequence[Dict[str, Any]],
        tokenize: bool = False,
        add_generation_prompt: bool = True,
        **_: Any,
    ) -> Any:
        rendered = []
        for msg in messages or []:
            role = str(msg.get("role", "user")).lower()
            content = msg.get("content", "")
            if not isinstance(content, str):
                content = json.dumps(content, ensure_ascii=False)
            if role == "assistant":
                rendered.append(f"<｜Assistant｜>{content}")
            elif role == "system":
                rendered.append(str(content))
            else:
                rendered.append(f"<｜User｜>{content}")
        if add_generation_prompt:
            rendered.append("<｜Assistant｜>")
        text = "".join(rendered)
        if tokenize:
            return text.split()
        return text


def build_local_prover_handler(name: str) -> Any:
    if name == "dpskcot":
        return DeepSeekCoTHandler()
    if name == "dpsknoncot":
        return DeepSeekNonCoTHandler()
    if name == "kiminacot":
        return KiminaCoTHandler()
    raise ValueError(f"Unknown local prover handler: {name}")


def is_deployed_local_prover_model(model: str) -> bool:
    m = (model or "").strip().lower()
    if not m or m == "symbolic":
        return False
    return not any(m.startswith(prefix) for prefix in COMMERCIAL_PROVER_PREFIXES)


def load_prover_base_url(args: argparse.Namespace) -> str:
    if args.prover_base_url:
        return args.prover_base_url.rstrip("/")
    config_path = Path(args.localhost_config)
    if not config_path.exists():
        raise FileNotFoundError(
            f"Local prover config not found: {config_path}. "
            "Pass --prover-base-url or deploy the vLLM server first."
        )
    with config_path.open("r", encoding="utf-8") as f:
        cfg = yaml.safe_load(f) or {}
    base_url = str(((cfg.get("prover_llm") or {}).get("base_url") or "")).strip()
    if not base_url:
        raise ValueError(
            f"{config_path} does not define prover_llm.base_url. "
            "Pass --prover-base-url or deploy the prover server first."
        )
    return base_url.rstrip("/")


def chat_messages_from_handler_output(messages: Any, prompt: str) -> Sequence[Dict[str, str]]:
    if isinstance(messages, list) and messages:
        out = []
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
        if out:
            return out
    return [{"role": "user", "content": prompt}]


def call_deployed_prover_chat(
    *,
    base_url: str,
    model: str,
    prompt: str,
    messages: Sequence[Dict[str, str]],
    args: argparse.Namespace,
) -> Dict[str, Any]:
    headers = {"Content-Type": "application/json"}
    api_key = os.environ.get("PROVER_LLM_API_KEY") or os.environ.get("VLLM_API_KEY")
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"

    if args.local_prover_api == "completions":
        payload = {
            "model": model,
            "prompt": prompt,
            "temperature": float(args.local_prover_temperature),
            "max_tokens": int(args.local_prover_max_tokens),
        }
        resp = requests.post(
            f"{base_url}/completions",
            headers=headers,
            json=payload,
            timeout=float(args.local_prover_timeout_s),
        )
        if not (200 <= resp.status_code < 300):
            body = resp.text
            if len(body) > 4000:
                body = body[:4000] + "\n...[truncated]"
            raise RuntimeError(f"HTTP {resp.status_code} from deployed prover completions: {body}")
        data = resp.json()
        try:
            text = data["choices"][0].get("text") or ""
        except Exception:
            text = json.dumps(data, ensure_ascii=False)[:20000]
        return {"text": text, "raw": data}

    payload = {
        "model": model,
        "messages": list(messages),
        "temperature": float(args.local_prover_temperature),
        "max_tokens": int(args.local_prover_max_tokens),
    }
    resp = requests.post(
        f"{base_url}/chat/completions",
        headers=headers,
        json=payload,
        timeout=float(args.local_prover_timeout_s),
    )
    if resp.status_code >= 500 and "non-streaming mode" in resp.text:
        payload["stream"] = True
        stream_resp = requests.post(
            f"{base_url}/chat/completions",
            headers=headers,
            json=payload,
            timeout=float(args.local_prover_timeout_s),
            stream=True,
        )
        if not (200 <= stream_resp.status_code < 300):
            body = stream_resp.text
            if len(body) > 4000:
                body = body[:4000] + "\n...[truncated]"
            raise RuntimeError(f"HTTP {stream_resp.status_code} from deployed prover stream: {body}")
        chunks = []
        raw_events = []
        for line in stream_resp.iter_lines(decode_unicode=True):
            if not line:
                continue
            if not line.startswith("data:"):
                continue
            data_text = line[len("data:"):].strip()
            if data_text == "[DONE]":
                break
            try:
                event = json.loads(data_text)
            except json.JSONDecodeError:
                continue
            raw_events.append(event)
            for choice in event.get("choices") or []:
                delta = choice.get("delta") or {}
                content = delta.get("content")
                if isinstance(content, str):
                    chunks.append(content)
        return {"text": "".join(chunks), "raw": {"stream_events": raw_events}}

    if not (200 <= resp.status_code < 300):
        body = resp.text
        if len(body) > 4000:
            body = body[:4000] + "\n...[truncated]"
        raise RuntimeError(f"HTTP {resp.status_code} from deployed prover: {body}")

    data = resp.json()
    text = ""
    try:
        text = data["choices"][0]["message"].get("content") or ""
    except Exception:
        text = json.dumps(data, ensure_ascii=False)[:20000]
    return {"text": text, "raw": data}


def compilation_result_from_repl(repl_result: Any) -> Dict[str, Any]:
    if not isinstance(repl_result, dict):
        text = str(repl_result)
        ok = "error:" not in text
        return {
            "pass": ok,
            "complete": ok and "sorry" not in text,
            "errors": [] if ok else [{"pos": {"line": 1, "column": 0}, "endPos": None, "data": text}],
            "warnings": [],
            "infos": [],
            "sorries": [],
            "system_errors": None,
        }

    messages = repl_result.get("messages") or []
    errors = [m for m in messages if isinstance(m, dict) and m.get("severity") == "error"]
    warnings = [m for m in messages if isinstance(m, dict) and m.get("severity") == "warning"]
    infos = [m for m in messages if isinstance(m, dict) and m.get("severity") == "info"]
    sorries = repl_result.get("sorries") or []
    pass_flag = not errors
    complete_flag = (
        pass_flag
        and not sorries
        and not any(
            "declaration uses 'sorry'" in str(w.get("data", ""))
            or "failed" in str(w.get("data", "")).lower()
            for w in warnings
        )
    )
    return {
        "pass": pass_flag,
        "complete": complete_flag,
        "errors": errors,
        "warnings": warnings,
        "infos": infos,
        "sorries": sorries,
        "system_errors": None,
    }


def safe_write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")
    tmp.replace(path)


def local_attempt_is_success(row: Dict[str, Any]) -> bool:
    comp = row.get("compilation_result") or {}
    return bool(comp.get("pass") and comp.get("complete"))


def compile_local_prover_attempts(
    attempts: Sequence[Dict[str, Any]],
    args: argparse.Namespace,
) -> Sequence[Dict[str, Any]]:
    workers = max(1, min(int(args.local_prover_compile_workers), len(attempts) or 1))

    def compile_one(attempt: Dict[str, Any]) -> Dict[str, Any]:
        code = str(attempt.get("full_code") or "")
        if not code.strip() or code.strip().lower() == "none" or attempt.get("inference_error"):
            comp = {
                "pass": False,
                "complete": False,
                "errors": [
                    {
                        "pos": {"line": 1, "column": 0},
                        "endPos": None,
                        "data": attempt.get("inference_error") or "Inference did not return a Lean code block.",
                    }
                ],
                "warnings": [],
                "infos": [],
                "sorries": [],
                "system_errors": None,
            }
        else:
            comp = compilation_result_from_repl(run_lean_code_repl(code))

        row = {
            "name": attempt["problem_id"],
            "problem_id": attempt["problem_id"],
            "origin_problem_id": attempt["origin_problem_id"],
            "code": code,
            "full_code": code,
            "model_output": attempt.get("model_output", ""),
            "messages_history_list": attempt.get("messages_history_list", []),
            "round": attempt.get("round", 0),
            "compilation_result": comp,
        }
        return row

    if not attempts:
        return []
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
        return list(executor.map(compile_one, attempts))


def run_deployed_local_prover_demo(
    *,
    entry: Dict[str, Any],
    eval_record: Dict[str, Any],
    args: argparse.Namespace,
    proof_root: Path,
) -> Dict[str, Any]:
    base_url = load_prover_base_url(args)
    handler = build_local_prover_handler(args.local_prover_handler)
    tokenizer = SimpleChatTemplateTokenizer()
    output_dir = proof_root / "deployed_local_prover" / sanitize_file_stem(entry["name"])
    output_dir.mkdir(parents=True, exist_ok=True)
    formal_statement_for_prover = replace_final_by_suffix(
        eval_record["formal_statement"], ":= by sorry"
    )

    print(f"[demo-local-prover] base_url={base_url}")
    print(f"[demo-local-prover] handler={args.local_prover_handler}")

    def make_initial_attempt(sample_idx: int) -> Dict[str, Any]:
        prompt, messages = handler.prover_inference(formal_statement_for_prover, tokenizer)
        return {
            "problem_id": f"{entry['name']}_g{sample_idx}",
            "origin_problem_id": entry["name"],
            "formal_statement": formal_statement_for_prover,
            "model_input": prompt,
            "messages_history_list": list(chat_messages_from_handler_output(messages, prompt)),
            "round": 0,
        }

    def make_correction_attempt(prev: Dict[str, Any], round_idx: int) -> Dict[str, Any]:
        error_message = get_error_str(
            prev.get("code") or prev.get("full_code") or "",
            prev.get("compilation_result") or {},
            error_thres=True,
        )
        prompt, messages = handler.generate_correction_prompt(
            lean4_code_original_stmt=formal_statement_for_prover,
            history_messages_from_prev_round=prev.get("messages_history_list", []),
            prev_round_llm_raw_output=prev.get("model_output", ""),
            error_message_for_prev_round=error_message,
            tokenizer=tokenizer,
            current_correction_round_num=round_idx,
            unsolved_goals_restart_hint=False,
        )
        return {
            "problem_id": f"{prev['problem_id']}_corr{round_idx}_g0",
            "origin_problem_id": entry["name"],
            "formal_statement": formal_statement_for_prover,
            "model_input": prompt,
            "messages_history_list": list(chat_messages_from_handler_output(messages, prompt)),
            "round": round_idx,
        }

    def query_one(attempt: Dict[str, Any]) -> Dict[str, Any]:
        out = dict(attempt)
        try:
            call = call_deployed_prover_chat(
                base_url=base_url,
                model=args.prover_model,
                prompt=attempt["model_input"],
                messages=attempt["messages_history_list"],
                args=args,
            )
            text = str(call.get("text") or "")
            extracted = handler.extrac_code(text)
            full_code = "None" if extracted in ("None", None) else handler.problem_check(
                formal_statement_for_prover, extracted
            )
            out.update(
                {
                    "model_output": text,
                    "api_raw": call.get("raw", {}),
                    "full_code": full_code,
                    "inference_error": "",
                }
            )
        except Exception as exc:
            out.update(
                {
                    "model_output": "",
                    "api_raw": {},
                    "full_code": "None",
                    "inference_error": f"{type(exc).__name__}: {exc}",
                }
            )
        return out

    def run_query_batch(attempts: Sequence[Dict[str, Any]], round_idx: int) -> Sequence[Dict[str, Any]]:
        parallel = args.local_prover_parallel
        if int(parallel) <= 0:
            parallel = len(attempts)
        parallel = max(1, min(int(parallel), len(attempts) or 1))
        print(f"[demo-local-prover] round {round_idx}: querying {len(attempts)} sample(s), parallel={parallel}")
        with concurrent.futures.ThreadPoolExecutor(max_workers=parallel) as executor:
            completed = list(executor.map(query_one, attempts))
        safe_write_json(output_dir / f"full_records_round{round_idx}.json", completed)
        return completed

    all_attempts = []
    all_compilations = []

    pending_attempts: Sequence[Dict[str, Any]] = [
        make_initial_attempt(i) for i in range(int(args.pass_at_n))
    ]
    successful_body = ""
    successful_attempt = ""

    for round_idx in range(0, int(args.correction_rounds) + 1):
        if not pending_attempts:
            break
        queried = run_query_batch(pending_attempts, round_idx)
        all_attempts.extend(queried)

        print(
            f"[demo-local-prover] round {round_idx}: compiling {len(queried)} attempt(s), "
            f"workers={args.local_prover_compile_workers}"
        )
        compiled = list(compile_local_prover_attempts(queried, args))
        safe_write_json(output_dir / f"code_compilation_round{round_idx}.json", compiled)
        all_compilations.extend(compiled)

        solved_rows = [row for row in compiled if local_attempt_is_success(row)]
        print(f"[demo-local-prover] round {round_idx}: solved {len(solved_rows)}/{len(compiled)}")
        if solved_rows:
            successful = solved_rows[0]
            successful_body = extract_proof_body(str(successful.get("code") or ""))
            successful_attempt = str(successful.get("name") or "")
            break

        if round_idx >= int(args.correction_rounds):
            break
        pending_attempts = [make_correction_attempt(row, round_idx + 1) for row in compiled]

    summary = {
        "name": entry["name"],
        "is_solved": bool(successful_body),
        "successful_attempt": successful_attempt,
        "attempts": len(all_attempts),
        "compiled_attempts": len(all_compilations),
        "output_dir": str(output_dir),
    }
    safe_write_json(output_dir / "summary.json", summary)
    safe_write_json(output_dir / "full_records.json", all_attempts)
    safe_write_json(output_dir / "code_compilation.json", all_compilations)

    return {
        "output_dir": str(output_dir),
        "summary_path": str(output_dir / "summary.json"),
        "proof_body": successful_body,
        "solved": bool(successful_body),
        "successful_attempt": successful_attempt,
    }


def print_section(title: str) -> None:
    print("\n" + "=" * 80)
    print(title)
    print("=" * 80)


def print_conjecturer_history(history_path: Path) -> None:
    if not history_path.exists():
        print("[demo] No conjecturer history file was written.")
        return
    print_section("Conjecturer Transcript")
    print(history_path.read_text(encoding="utf-8"))


def maybe_manual_fallback(
    entry: Dict[str, Any],
    answer: str,
    args: argparse.Namespace,
) -> Tuple[Optional[str], str]:
    raw = read_text_arg(
        direct=args.fallback_proof,
        path=args.fallback_proof_file,
        stdin_if_missing=False,
    )
    if not raw.strip():
        return None, ""

    proof_body = extract_proof_body(raw)
    substituted = f"{ecp_preamble(entry)}\n{answer_substituted_theorem(entry, answer)}{proof_body}\n"
    print("[demo] Verifying manual fallback proof body against the answer-substituted theorem.")
    result = run_lean_code(substituted)
    if answer_check_passed(result):
        return proof_body, "manual_fallback"
    print("[demo] Manual fallback proof did not compile:")
    print(result)
    return None, ""


def write_and_verify_assembled_proof(
    entry: Dict[str, Any],
    answer: str,
    proof_body: str,
    args: argparse.Namespace,
    source: str,
) -> Optional[Path]:
    assembled = assemble_existential_proof(entry, answer, proof_body)
    check = run_lean_code(assembled)
    if not answer_check_passed(check):
        use_only = assemble_existential_proof(entry, answer, "")
        use_only_check = run_lean_code(use_only)
        if answer_check_passed(use_only_check):
            assembled = use_only
            check = use_only_check
            source = f"{source}+use_only"

    demo_dir = Path(args.formalization_demo_dir)
    demo_dir.mkdir(parents=True, exist_ok=True)
    path = demo_dir / f"{sanitize_file_stem(entry['name'])}_{now_tag()}.lean"
    path.write_text(assembled, encoding="utf-8")

    print(f"[demo] Wrote assembled proof to {path}")
    file_check = run_lean_file(str(path))
    if not answer_check_passed(file_check):
        check = file_check
    if answer_check_passed(check):
        print(f"[demo] Assembled full proof verified by Lean (source={source}).")
    else:
        print("[demo] Assembled proof was written, but Lean reported an error:")
        print(check)

    if args.show_proof:
        print_section("Assembled Full Proof")
        print(assembled)
    return path


def run_ecp_demo(args: argparse.Namespace) -> int:
    source = read_text_arg(
        direct=args.theorem,
        path=args.theorem_file,
        stdin_if_missing=True,
    )
    if not source.strip():
        raise ValueError("Provide a theorem with --theorem, --theorem-file, or stdin.")

    entry = entry_from_theorem_source(source, args)
    cpu = args.cpu if int(args.cpu) > 0 else (os.cpu_count() or 1)
    root = Path(args.output_dir) / f"{sanitize_file_stem(entry['name'])}_{now_tag()}"
    answer_dir = root / "answer_construction"
    answer_dir.mkdir(parents=True, exist_ok=True)

    print(f"[demo] theorem={entry['name']}")
    print(f"[demo] answer binder={entry['answer_name']} : {entry['answer_type']}")
    print(f"[demo] admissible_vocabulary={entry['formal_answer_info']['admissible_vocabulary']}")
    print(f"[demo] conjecturer_model={args.conjecturer_model}, baseline={args.baseline}")

    result = construct_answer_for_entry(
        entry=entry,
        output_dir=str(answer_dir),
        temp_formalization_dir=args.temp_formalization_dir,
        baseline=args.baseline,
        conjecturer_model=args.conjecturer_model,
        current_round=1,
    )

    history_path = answer_dir / "llm_history" / "conjecturer" / f"{entry['name']}.txt"
    if args.show_conjecturer_history:
        print_conjecturer_history(history_path)

    answer = str(result.get("proposed_answer", "")).strip()
    print_section("Answer Construction Result")
    print(f"answer_ok: {result.get('answer_ok')}")
    print(f"proposed_answer: {answer}")
    if result.get("answer_error"):
        print(f"answer_error: {result.get('answer_error')}")

    if not is_true_value(result.get("answer_ok")):
        print("[demo] Stopping before proof generation because the constructed answer failed syntax/admissibility checks.")
        return 2

    eval_path = root / "prover_eval_temp.jsonl"
    records = build_prover_records([result], [entry], negated=False)
    write_jsonl(str(eval_path), records)

    print_section("Proof Generation")
    print(
        f"[demo] prover_model={args.prover_model}, pass@{args.pass_at_n}, "
        f"correction_rounds={args.correction_rounds}"
    )
    proof_root = root / "proof_generation"
    if is_deployed_local_prover_model(args.prover_model):
        proof_info = run_deployed_local_prover_demo(
            entry=entry,
            eval_record=records[0],
            args=args,
            proof_root=proof_root,
        )
        solved_map = {entry["name"]: bool(proof_info.get("solved"))}
        proof_body = str(proof_info.get("proof_body") or "")
        proof_source = "deployed_local_prover" if proof_body else ""
    else:
        proof_info = run_proof_gen(
            problem_path="demo",
            prover_model=args.prover_model,
            output_dir=str(proof_root),
            eval_file_path=str(eval_path),
            pass_at_n=args.pass_at_n,
            correction_samples=1,
            correction_rounds=args.correction_rounds,
            gpu=args.gpu,
            cpu=cpu,
            nodes=args.nodes,
            negated=False,
            max_model_len=args.max_model_len,
            run_tag=f"{sanitize_file_stem(entry['name'])}_final",
        )

        solved_map = read_final_summary(proof_info["summary_path"])
        proof_bodies = load_successful_proof_bodies(proof_info["output_dir"])
        proof_body = proof_bodies.get(entry["name"])
        proof_source = "goedel_pipeline" if proof_body else ""

    if not proof_body and args.enable_final_automation:
        print("[demo] No successful prover proof found; trying fixed automation fallback.")
        automation_solved, automation_bodies = run_final_automation_fallback(
            final_eval_path=str(eval_path),
            failed_names={entry["name"]},
            output_dir=str(proof_root),
            cpu=cpu,
            nodes=args.nodes,
        )
        if automation_solved.get(entry["name"]) and automation_bodies.get(entry["name"]):
            proof_body = automation_bodies[entry["name"]]
            proof_source = "automation_fallback"

    if not proof_body:
        manual_body, manual_source = maybe_manual_fallback(entry, answer, args)
        if manual_body:
            proof_body = manual_body
            proof_source = manual_source

    print_section("Proof Generation Result")
    print(f"prover_solved: {bool(solved_map.get(entry['name'], False) or proof_body)}")
    print(f"proof_source: {proof_source or 'none'}")
    print(f"proof_output_dir: {proof_info['output_dir']}")

    if not proof_body:
        print("[demo] No compiling proof body was found, so no full existential proof was assembled.")
        return 3

    write_and_verify_assembled_proof(entry, answer, proof_body, args, proof_source)
    return 0


def header_and_type_for_check(args: argparse.Namespace) -> Tuple[str, str, str]:
    source = read_text_arg(
        direct=args.theorem,
        path=args.theorem_file,
        stdin_if_missing=False,
    )
    if source.strip():
        entry = entry_from_theorem_source(source, args)
        return ecp_preamble(entry), entry["answer_type"], entry["name"]

    header = read_text_arg(direct=args.header, path=args.header_file) or DEFAULT_HEADER
    answer_type = args.answer_type
    if not answer_type:
        raise ValueError("Provide --answer-type, or provide --theorem/--theorem-file so it can be inferred.")
    return header, answer_type, args.problem_name or "demo_check"


def run_admissibility_demo(args: argparse.Namespace) -> int:
    answer = read_text_arg(direct=args.answer, path=args.answer_file, stdin_if_missing=True).strip()
    if not answer:
        raise ValueError("Provide an answer with --answer, --answer-file, or stdin.")

    header, answer_type, _ = header_and_type_for_check(args)
    info = admissibility_info_from_args(args)
    check_info = {
        "header": header,
        "answer_type": answer_type,
        **info,
    }

    print(f"[admissible] answer_type={answer_type}")
    print(f"[admissible] admissible_vocabulary={info['admissible_vocabulary']}")
    syntax_ok, syntax_result = verify_answer_syntax(header, answer, answer_type)
    print(f"[admissible] syntax_ok={syntax_ok}")
    if not syntax_ok:
        print(syntax_result)
        return 2

    admissible = verify_answer_admissibility(answer, check_info)
    print(f"[admissible] admissible={admissible}")
    if args.verbose:
        print("[admissible] Raw canonical checker output:")
        lean_code = (
            "import utils.canonical_all_in_one\n"
            f"{header}\n"
            f"#isCanonical ({answer}:{answer_type}) with admissible_vocabulary := "
            f"{info['admissible_vocabulary']} "
            f"{QUANTIFIER_OPTION_KEY} := "
            f"{'true' if bool(check_info[QUANTIFIER_OPTION_KEY]) else 'false'}"
            + "\n"
        )
        print(run_lean_code(lean_code))
    return 0 if admissible else 1


def run_equivalence_demo(args: argparse.Namespace) -> int:
    candidate = read_text_arg(direct=args.candidate_answer, path=args.candidate_answer_file).strip()
    ground_truth = read_text_arg(direct=args.ground_truth_answer, path=args.ground_truth_answer_file).strip()
    if not candidate or not ground_truth:
        raise ValueError("Provide --candidate-answer and --ground-truth-answer, or their file variants.")

    header, answer_type, name = header_and_type_for_check(args)

    print(f"[equiv] answer_type={answer_type}")
    print(f"[equiv] candidate={candidate}")
    print(f"[equiv] ground_truth={ground_truth}")

    if args.equivalence_method == "automation":
        status = formal_equivalence_checker(
            name=name,
            header=header,
            answer_type=answer_type,
            answer_1=ground_truth,
            answer_2=candidate,
        )
        print(f"[equiv] automation_equivalent={status}")
        return 0 if is_true_value(status) else 1

    cpu = args.cpu if int(args.cpu) > 0 else (os.cpu_count() or 1)
    root = Path(args.output_dir) / f"{sanitize_file_stem(name)}_equiv_{now_tag()}"
    root.mkdir(parents=True, exist_ok=True)
    eval_path = root / "equivalence_eval.jsonl"
    formal_statement = (
        "import utils.fol\n"
        f"{header}\n"
        f"theorem {sanitize_lean_ident(name)}_candidate_eq_ground_truth : "
        f"({ground_truth} : {answer_type}) = ({candidate} : {answer_type}) := by "
    )
    write_jsonl(
        str(eval_path),
        [
            {
                "name": name,
                "split": "demo",
                "informal_prefix": "",
                "formal_statement": formal_statement,
                "lean4_code": formal_statement,
                "header": header,
                "answer_type": answer_type,
                "actual_answer": ground_truth,
                "proposed_answer": candidate,
                "equality_check": True,
            }
        ],
    )

    print(
        f"[equiv] proving equality with {args.prover_model}, pass@{args.pass_at_n}, "
        f"correction_rounds={args.correction_rounds}"
    )
    proof_info = run_proof_gen(
        problem_path="demo_equivalence",
        prover_model=args.prover_model,
        output_dir=str(root),
        eval_file_path=str(eval_path),
        pass_at_n=args.pass_at_n,
        correction_samples=1,
        correction_rounds=args.correction_rounds,
        gpu=args.gpu,
        cpu=cpu,
        nodes=args.nodes,
        negated=False,
        max_model_len=args.max_model_len,
        run_tag=f"{sanitize_file_stem(name)}_equivalence",
    )
    solved = read_final_summary(proof_info["summary_path"]).get(name, False)
    print(f"[equiv] proved_equivalent={bool(solved)}")
    print(f"[equiv] proof_output_dir={proof_info['output_dir']}")

    if args.show_proof and solved:
        bodies = load_successful_proof_bodies(proof_info["output_dir"])
        body = bodies.get(name, "")
        if body:
            print_section("Equivalence Proof Body")
            print(body)
    return 0 if solved else 1


def add_common_model_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--conjecturer-model", default="gpt-5.4")
    parser.add_argument("--prover-model", default="gpt-5.4")
    parser.add_argument("--baseline", choices=["cot", "mcp"], default="mcp")
    parser.add_argument("--output-dir", default="output/demo")
    parser.add_argument("--temp-formalization-dir", default="Formalization/cache/demo")
    parser.add_argument("--pass-at-n", type=int, default=2)
    parser.add_argument("--correction-rounds", type=int, default=2)
    parser.add_argument("--gpu", type=int, default=4)
    parser.add_argument("--cpu", type=int, default=0)
    parser.add_argument("--nodes", type=int, default=1)
    parser.add_argument("--max-model-len", type=int, default=DEFAULT_PROVER_MAX_MODEL_LEN)
    parser.add_argument("--localhost-config", default="configs/localhost.yaml")
    parser.add_argument("--prover-base-url", default="", help="Override prover_llm.base_url for deployed local prover models.")
    parser.add_argument("--local-prover-handler", choices=["dpskcot", "dpsknoncot", "kiminacot"], default="dpskcot")
    parser.add_argument("--local-prover-api", choices=["completions", "chat"], default="completions")
    parser.add_argument("--local-prover-parallel", type=int, default=0, help="Parallel HTTP requests for deployed local prover; 0 uses the batch size.")
    parser.add_argument("--local-prover-compile-workers", type=int, default=4)
    parser.add_argument("--local-prover-max-tokens", type=int, default=8192)
    parser.add_argument("--local-prover-timeout-s", type=float, default=600.0)
    parser.add_argument("--local-prover-temperature", type=float, default=1.0)


def add_theorem_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--theorem", default="", help="Lean theorem statement or full Lean source containing one theorem.")
    parser.add_argument("--theorem-file", default="", help="Path to a Lean file/source containing one theorem.")
    parser.add_argument("--problem-name", default="", help="Optional display/output name; defaults to the Lean theorem name.")
    parser.add_argument("--header", default="", help="Lean header for check modes when no theorem is provided.")
    parser.add_argument("--header-file", default="", help="Path to Lean header for check modes when no theorem is provided.")
    parser.add_argument("--answer-type", default="", help="Answer type for check modes when no theorem is provided.")


def add_admissibility_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--level",
        choices=sorted(LEVEL_VOCABULARIES),
        default="basic",
        help="Demo vocabulary preset. Ignored when --admissible-vocabulary is provided.",
    )
    parser.add_argument(
        "--admissible-vocabulary",
        default="",
        help="Lean list like '[``OfNat.ofNat]' or a comma/space-separated list like 'OfNat.ofNat,HAdd.hAdd'.",
    )
    parser.add_argument("--allow-quantifier", type=parse_bool, default=None)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Single-problem ECP demo: construct an answer, prove the substituted theorem, and assemble the existential proof.",
    )
    parser.add_argument("--mode", choices=["ecp", "equiv", "admissible"], default="ecp")
    add_common_model_args(parser)
    add_theorem_args(parser)
    add_admissibility_args(parser)

    parser.add_argument("--formalization-demo-dir", default="Formalization/demo")
    parser.add_argument("--show-conjecturer-history", type=parse_bool, default=True)
    parser.add_argument("--show-proof", type=parse_bool, default=True)
    parser.add_argument("--enable-final-automation", type=parse_bool, default=True)
    parser.add_argument("--fallback-proof", default="", help="Optional manual proof body fallback for --mode ecp.")
    parser.add_argument("--fallback-proof-file", default="", help="Optional file containing a manual proof body fallback.")

    parser.add_argument("--answer", default="", help="Answer expression for --mode admissible.")
    parser.add_argument("--answer-file", default="", help="File containing answer expression for --mode admissible.")
    parser.add_argument("--candidate-answer", default="", help="Candidate answer expression for --mode equiv.")
    parser.add_argument("--candidate-answer-file", default="", help="File containing candidate answer expression for --mode equiv.")
    parser.add_argument("--ground-truth-answer", default="", help="Ground-truth answer expression for --mode equiv.")
    parser.add_argument("--ground-truth-answer-file", default="", help="File containing ground-truth answer expression for --mode equiv.")
    parser.add_argument("--equivalence-method", choices=["prover", "automation"], default="prover")
    parser.add_argument("--verbose", action="store_true")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        if args.mode == "ecp":
            return run_ecp_demo(args)
        if args.mode == "equiv":
            return run_equivalence_demo(args)
        if args.mode == "admissible":
            return run_admissibility_demo(args)
        raise AssertionError(args.mode)
    except Exception as exc:
        print(f"[demo] ERROR: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
