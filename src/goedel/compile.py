import json
import sys
import os
import argparse
import random
import re
from typing import Any, Dict, List, Optional

import numpy as np
import pandas as pd

import ray  # NEW: use Ray for CPU data-parallel

parent_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
if parent_dir not in sys.path:
    sys.path.append(parent_dir)

from src.goedel.repl_scheduler import DEFAULT_IMPORTS, scheduler


AUTOMATION_PROOF_BODY = "\n  try native_decide\n  try simp\n  try aesop\n  try nlinarith\n  try ring\n  try norm_num\n"


def split_list_randomly(lst, k):
    """Shuffle lst and split into k approximately equal parts."""
    random.shuffle(lst)
    return list(map(list, np.array_split(lst, k)))


def handle(text):
    lines = text.split('\n')

    filtered_lines = [
        line for line in lines
        if not (
            line.strip().startswith('import') or
            line.strip().startswith('set_option') or
            line.strip().startswith('open')
        )
    ]

    return '\n'.join(filtered_lines)


def normalize_code_text(x):
    if x is None:
        return ""
    s = str(x).strip()
    if s.lower() in {"none", "null", "nan"}:
        return ""
    return handle(s)


def _text_is_empty(value: Any) -> bool:
    return not isinstance(value, str) or not value.strip()


def _generated_failure_reason(row: Dict[str, Any], code: str) -> str:
    reasons: List[str] = []
    inference_error = row.get("inference_error")
    if inference_error:
        reasons.append(f"inference_error={inference_error}")
    if "model_output" in row and _text_is_empty(row.get("model_output")):
        reasons.append("empty model_output")
    if "full_code" in row and not code:
        reasons.append("empty full_code")
    elif "code" in row and not code:
        reasons.append("empty code")
    if reasons:
        return "; ".join(str(x) for x in reasons)
    return ""


def _synthetic_generation_failure(row: Dict[str, Any]) -> Dict[str, Any]:
    reason = row.get("generated_code_failure_reason") or "inference did not produce compilable Lean code"
    return {
        "code": row.get("original_code", ""),
        "compilation_result": {
            "pass": False,
            "complete": False,
            "system_errors": None,
            "errors": [
                {
                    "pos": {"line": 1, "column": 0},
                    "endPos": None,
                    "data": f"Inference did not produce compilable Lean code: {reason}",
                }
            ],
            "inference_failure": True,
        },
        "env": None,
        "name": row.get("name"),
        "verify_time": 0.0,
    }


def _origin_from_generation_id(problem_id: str) -> str:
    text = str(problem_id or "")
    match = re.match(r"^(?P<origin>.+?)_g\d+(?:_corr\d+_g\d+)*$", text)
    if match:
        return match.group("origin")
    return text


def _read_json_or_jsonl(path: str) -> List[Dict[str, Any]]:
    if not path or not os.path.exists(path):
        return []
    if path.endswith(".jsonl"):
        rows: List[Dict[str, Any]] = []
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                if isinstance(row, dict):
                    rows.append(row)
        return rows
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    return data if isinstance(data, list) else []


def _normalize_admissible_vocabulary(value: Any) -> str:
    if isinstance(value, str):
        text = value.strip()
        return text if text else "[]"
    if isinstance(value, list):
        items = [str(x).strip() for x in value if str(x).strip()]
        return "[" + ", ".join(items) + "]" if items else "[]"
    return "[]"


QUANTIFIER_OPTION_KEY = "allow_quantifier"
QUANTIFIER_OPTION_DEFAULT = True


def _normalize_bool_option(value: Any, default: bool = True) -> bool:
    if value is None:
        return default
    if isinstance(value, bool):
        return value
    text = str(value).strip().lower()
    if text in {"true", "1", "yes", "y"}:
        return True
    if text in {"false", "0", "no", "n"}:
        return False
    return default


def _structural_options_from_sources(row: Dict[str, Any], info: Dict[str, Any]) -> Dict[str, bool]:
    quantifier_value = _normalize_bool_option(
        row.get(QUANTIFIER_OPTION_KEY, info.get(QUANTIFIER_OPTION_KEY)),
        QUANTIFIER_OPTION_DEFAULT,
    )
    return {QUANTIFIER_OPTION_KEY: quantifier_value}


def _format_structural_options(options: Dict[str, Any]) -> str:
    value = _normalize_bool_option(options.get(QUANTIFIER_OPTION_KEY), QUANTIFIER_OPTION_DEFAULT)
    return f"{QUANTIFIER_OPTION_KEY} := {'true' if value else 'false'}"


def _metadata_from_row(row: Dict[str, Any]) -> Dict[str, Any]:
    info = row.get("formal_answer_info") or {}
    if not isinstance(info, dict):
        info = {}
    admissible = row.get("admissible_vocabulary") or info.get("admissible_vocabulary") or "[]"
    out: Dict[str, Any] = {
        "answer_type": str(row.get("answer_type") or ""),
        "admissible_vocabulary": _normalize_admissible_vocabulary(admissible),
        "theorem_name": str(row.get("theorem_name") or row.get("name") or ""),
        QUANTIFIER_OPTION_KEY: _structural_options_from_sources(row, info)[QUANTIFIER_OPTION_KEY],
    }
    return out


def _load_admissibility_metadata(path: str) -> Dict[str, Dict[str, Any]]:
    out: Dict[str, Dict[str, Any]] = {}
    for row in _read_json_or_jsonl(path):
        name = row.get("name") or row.get("origin_problem_id") or row.get("problem_id")
        if not name:
            continue
        origin = _origin_from_generation_id(str(name))
        out[origin] = _metadata_from_row(row)
    return out


def _extract_theorem_name(code: str) -> str:
    match = re.search(r"(?:^|\s)theorem\s+([A-Za-z_][A-Za-z0-9_'.]*)\b", code or "")
    return match.group(1) if match else ""


def _add_lean_import(imports: str, module: str) -> str:
    lines = imports.splitlines()
    import_line = f"import {module}"
    if import_line in [line.strip() for line in lines]:
        return imports
    insert_at = 0
    while insert_at < len(lines) and lines[insert_at].strip().startswith("import "):
        insert_at += 1
    lines.insert(insert_at, import_line)
    return "\n".join(lines).rstrip() + "\n"


def _append_witness_admissibility_check(
    code: str,
    theorem_name: str,
    admissible_vocabulary: str,
    structural_options: Dict[str, Any],
) -> str:
    theorem_name = (theorem_name or _extract_theorem_name(code)).strip()
    if not theorem_name:
        return code
    allowed = _normalize_admissible_vocabulary(admissible_vocabulary)
    structural = _format_structural_options(structural_options)
    return (
        f"{code.rstrip()}\n\n"
        f"#check_first_exists_witness_canonical {theorem_name} "
        f"with admissible_vocabulary := {allowed} {structural}\n"
    )


def _append_automation_tactics(code: str) -> str:
    """Append the fixed tactic portfolio to a theorem stub ending in `:= by`."""
    text = (code or "").rstrip()
    if not re.search(r":=\s*by\s*$", text, flags=re.DOTALL):
        return code
    return f"{text}{AUTOMATION_PROOF_BODY}"


def _extract_backtick_blocks_text(resp: Any) -> List[str]:
    s = resp if isinstance(resp, str) else json.dumps(resp, ensure_ascii=False)
    return [b.strip().rstrip().replace("\n", "") for b in re.findall(r"```(.*?)```", s, flags=re.DOTALL)]


def _witness_status_from_infos(infos: Any) -> Optional[str]:
    blocks: List[str] = []
    for info in infos or []:
        if isinstance(info, dict):
            blocks.extend(_extract_backtick_blocks_text(info.get("data", "")))
    for block in blocks:
        status = block.strip()
        if status in {"canonical", "not canonical"}:
            return status
    return None


def _witness_failure_error(status: Optional[str]) -> Dict[str, Any]:
    if status == "not canonical":
        message = (
            "The proof constructs an outermost existential witness that is not canonical under "
            "this problem's admissible vocabulary. Please replace the existential witness with "
            "a simpler admissible answer and prove the theorem using that witness."
        )
    else:
        message = (
            "The proof was accepted by Lean, but the verifier could not extract and canonical-check "
            "the witness used for the theorem's outermost existential quantifier."
        )
    return {
        "pos": {"line": 1, "column": 0},
        "endPos": None,
        "data": message,
    }


def _prepare_codes(
    rows: List[Dict[str, Any]],
    *,
    enable_automation_tactics: bool,
    enable_witness_admissibility_check: bool,
    metadata_by_name: Dict[str, Dict[str, Any]],
) -> List[Dict[str, Any]]:
    codes: List[Dict[str, Any]] = []
    for row in rows:
        if "problem_id" in row:
            name = str(row.get("problem_id"))
            problem_id = name
        elif "name" in row:
            name = str(row.get("name"))
            problem_id = name
        else:
            raise RuntimeError(
                f"[compile] input row has keys {list(row.keys())} but needs either 'problem_id' or 'name'."
            )

        origin = str(row.get("origin_problem_id") or _origin_from_generation_id(problem_id))
        meta = metadata_by_name.get(origin, {})
        if "full_code" in row:
            code = normalize_code_text(row.get("full_code"))
        elif "code" in row:
            code = normalize_code_text(row.get("code"))
        elif "formal_statement" in row:
            code = normalize_code_text(row.get("formal_statement"))
        elif "lean4_code" in row:
            code = normalize_code_text(row.get("lean4_code"))
        else:
            code = ""
        generated_code_failure_reason = _generated_failure_reason(row, code)

        answer_type = str(row.get("answer_type") or meta.get("answer_type") or "")
        admissible = _normalize_admissible_vocabulary(
            row.get("admissible_vocabulary") or meta.get("admissible_vocabulary") or "[]"
        )
        structural_options = _structural_options_from_sources(row, meta)
        theorem_name = str(row.get("theorem_name") or meta.get("theorem_name") or origin or _extract_theorem_name(code))
        should_append_automation = bool(enable_automation_tactics)
        if should_append_automation and code:
            code = _append_automation_tactics(code)
        original_code = code
        should_check = bool(enable_witness_admissibility_check)
        if should_check and code:
            code = _append_witness_admissibility_check(code, theorem_name, admissible, structural_options)

        codes.append(
            {
                "name": name,
                "code": code,
                "problem_id": problem_id,
                "origin_problem_id": origin,
                "original_code": original_code,
                "answer_type": answer_type,
                "admissible_vocabulary": admissible,
                **structural_options,
                "theorem_name": theorem_name,
                "automation_tactics_enabled": should_append_automation,
                "witness_admissibility_check_enabled": should_check,
                "inference_error": row.get("inference_error") or "",
                "generated_code_failure_reason": generated_code_failure_reason,
            }
        )
    return codes


def _finalize_outputs(outputs: List[Dict[str, Any]], prepared_by_name: Dict[str, Dict[str, Any]]) -> List[Dict[str, Any]]:
    finalized: List[Dict[str, Any]] = []
    for row in outputs:
        prepared = prepared_by_name.get(str(row.get("name")))
        if not prepared:
            finalized.append(row)
            continue

        if "original_code" in prepared:
            row["code"] = prepared["original_code"]
        for key in (
            "problem_id",
            "origin_problem_id",
            "answer_type",
            "theorem_name",
            "automation_tactics_enabled",
            "witness_admissibility_check_enabled",
            "inference_error",
            "generated_code_failure_reason",
            QUANTIFIER_OPTION_KEY,
        ):
            row[key] = prepared.get(key)

        if prepared.get("witness_admissibility_check_enabled"):
            comp = row.get("compilation_result") or {}
            status = _witness_status_from_infos(comp.get("infos"))
            comp["witness_admissibility_checked"] = True
            comp["witness_admissibility_status"] = status or "not_run"
            if comp.get("pass") and comp.get("complete") and status != "canonical":
                comp["pass"] = False
                comp["complete"] = False
                errors = list(comp.get("errors") or [])
                errors.append(_witness_failure_error(status))
                comp["errors"] = errors
            row["compilation_result"] = comp
        finalized.append(row)
    return finalized


def build_arg_parser():
    parser = argparse.ArgumentParser()
    # 'results/test/to_inference_codes.json'
    parser.add_argument('--input_path', default="", type=str)
    # 'results/test/code_compilation.json'
    parser.add_argument('--output_path', default="", type=str)
    parser.add_argument('--cpu', default=64, type=int,
                        help="Number of CPU workers per node (for scheduler).")
    parser.add_argument('--node', default=1, type=int,
                        help="Number of Ray nodes / data-parallel partitions.")
    parser.add_argument('--metadata_path', default="", type=str,
                        help="Optional JSON/JSONL records with per-problem admissible_vocabulary metadata.")
    parser.add_argument('--enable_witness_admissibility_check', action='store_true',
                        help="Check outer existential witnesses against per-problem admissible_vocabulary.")
    parser.add_argument('--enable_automation_tactics', action='store_true',
                        help="Append the fixed automation tactic portfolio to theorem stubs before compiling.")

    return parser


@ray.remote
def run_scheduler_remote(codes_chunk, num_workers, imports):
    """
    Remote wrapper around scheduler for a single chunk of codes.
    We re-import inside to be safe in Ray workers.
    """
    from src.goedel.repl_scheduler import scheduler as _scheduler
    return _scheduler(codes_chunk, num_workers=num_workers, imports=imports)

def main():
    parser = build_arg_parser()
    args = parser.parse_args()

    if not args.input_path:
        print("Error: --input_path must be provided.")
        sys.exit(1)
    if not args.output_path:
        print("Error: --output_path must be provided.")
        sys.exit(1)

    input_file_path = args.input_path

    with open(input_file_path, 'r') as json_file:
        codes_json = json.load(json_file)

    # -------------------------------
    # NEW: handle empty inference output
    # -------------------------------
    if not isinstance(codes_json, list):
        raise RuntimeError(f"Expected a JSON list in {input_file_path}, got {type(codes_json)}")
    if len(codes_json) == 0:
        print(f"[compile] Input is empty ({input_file_path}). Writing empty outputs to {args.output_path} and exiting.")
        with open(args.output_path, 'w') as out_f:
            json.dump([], out_f, indent=4)
        return
    # -------------------------------

    metadata_by_name = (
        _load_admissibility_metadata(args.metadata_path)
        if args.enable_witness_admissibility_check
        else {}
    )
    codes = _prepare_codes(
        codes_json,
        enable_automation_tactics=args.enable_automation_tactics,
        enable_witness_admissibility_check=args.enable_witness_admissibility_check,
        metadata_by_name=metadata_by_name,
    )
    prepared_by_name = {row["name"]: row for row in codes}
    synthetic_outputs = [
        _synthetic_generation_failure(row)
        for row in codes
        if row.get("generated_code_failure_reason")
    ]
    runnable_codes = [
        row for row in codes
        if not row.get("generated_code_failure_reason")
    ]

    total_codes = len(codes)
    print(f"Total codes: {total_codes}")
    if synthetic_outputs:
        print(
            f"[compile] Skipping Lean for {len(synthetic_outputs)} terminal failed generation(s); "
            "writing synthetic failed compilation rows."
        )
    imports = DEFAULT_IMPORTS
    if args.enable_witness_admissibility_check:
        imports = _add_lean_import(imports, "utils.extract_exists_witness")
        print("[compile] witness admissibility check enabled")
    if args.enable_automation_tactics:
        print("[compile] automation tactic fallback enabled")

    if not runnable_codes:
        outputs_list = _finalize_outputs(synthetic_outputs, prepared_by_name)
        with open(args.output_path, 'w') as json_file:
            json.dump(outputs_list, json_file, indent=4)
        print(f"[compile] No runnable Lean code. Saved synthetic outputs to {args.output_path}")
        return

    # -------- Single-node path (no Ray data-parallel) --------
    if args.node <= 1:
        print("Running single-node compile (no Ray data-parallel).")
        random.shuffle(runnable_codes)
        outputs_list = synthetic_outputs + scheduler(runnable_codes, num_workers=args.cpu, imports=imports)
        outputs_list = _finalize_outputs(outputs_list, prepared_by_name)

        with open(args.output_path, 'w') as json_file:
            json.dump(outputs_list, json_file, indent=4)
        print(f"Saved outputs to {args.output_path}")
        return

    # -------- Multi-node data-parallel with Ray --------
    print(f"Running multi-node compile with Ray, nodes={args.node}.")
    ray.init(address="auto")

    partitions = split_list_randomly(runnable_codes, args.node)
    for i, part in enumerate(partitions):
        print(f"Partition {i}: {len(part)} codes")

    result_refs = []
    for idx, codes_chunk in enumerate(partitions):
        if not codes_chunk:
            continue
        ref = run_scheduler_remote.options(num_cpus=args.cpu).remote(codes_chunk, num_workers=args.cpu, imports=imports)
        result_refs.append(ref)

    results = ray.get(result_refs)

    outputs_list = list(synthetic_outputs)
    for partial in results:
        outputs_list.extend(partial)
    outputs_list = _finalize_outputs(outputs_list, prepared_by_name)

    with open(args.output_path, 'w') as json_file:
        json.dump(outputs_list, json_file, indent=4)

    print(f"Saved combined outputs to {args.output_path}")
if __name__ == "__main__": 
    main()
