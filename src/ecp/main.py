import argparse
import concurrent.futures
import json
import os
import re
import subprocess
import sys
import threading
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

from tqdm import tqdm

from src.ecp.agent import Conjecturer
from src.ecp.utils import (
    answer_substituted_theorem,
    assemble_existential_proof,
    auto_set_cuda_visible_devices,
    ecp_preamble,
    extract_proof_body,
    formal_equivalence_checker,
    full_problem_statement,
    is_true_value,
    run_lean_code,
)


DEFAULT_PROVER_MAX_MODEL_LEN = 30000
QUANTIFIER_OPTION_KEY = "allow_quantifier"

def parse_bool(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    return str(value).strip().lower() in {"1", "true", "yes", "y"}


def _answer_quantifier_option(info: Dict[str, Any]) -> str:
    if QUANTIFIER_OPTION_KEY in info:
        return "True" if parse_bool(info.get(QUANTIFIER_OPTION_KEY)) else "False"
    return "False"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="ECP: answer construction + Lean proof generation for existential theorem statements."
    )
    parser.add_argument("--mode", choices=["answer_gen", "proof_gen", "ecp", "llm_baseline"], default="ecp")
    parser.add_argument("--problem_path", type=str, default="putnam")
    parser.add_argument("--problem_name", type=str, default="all")
    parser.add_argument("--enable_problem_name_filter", type=parse_bool, default=False)
    parser.add_argument("--problem_name_list", type=str, default="")

    parser.add_argument("--conjecturer_model", type=str, default="gpt-5.4")
    parser.add_argument("--prover_model", type=str, default="Goedel-LM/Goedel-Prover-V2-32B")
    parser.add_argument("--baseline", choices=["cot", "mcp"], default="mcp")


    parser.add_argument("--output_dir", type=str, default="output")
    parser.add_argument("--temp_formalization_dir", type=str, default="Formalization/cache")
    parser.add_argument("--resume", type=parse_bool, default=True)

    parser.add_argument("--pass_at_n", type=int, default=32)
    parser.add_argument("--correction_rounds", type=int, default=2)
    parser.add_argument("--equivalence_prover_model", type=str, default="Goedel-LM/Goedel-Prover-V2-8B")
    parser.add_argument("--equivalence_pass_at_n", type=int, default=4)
    parser.add_argument("--equivalence_correction_rounds", type=int, default=2)
    parser.add_argument("--gpu", type=int, default=4)
    parser.add_argument("--cpu", type=int, default=0, help="CPU workers; default uses os.cpu_count().")
    parser.add_argument("--nodes", type=int, default=1)
    parser.add_argument("--max_model_len", type=int, default=DEFAULT_PROVER_MAX_MODEL_LEN)
    parser.add_argument("--eval_file_path", type=str, default="")
    parser.add_argument("--prover_tag", type=str, default="")

    parser.add_argument("--enable_enhanced_equivalence", type=parse_bool, default=True)
    parser.add_argument("--enable_negated_proof", type=parse_bool, default=True)
    parser.add_argument("--enable_final_automation", type=parse_bool, default=True)
    parser.add_argument("--max_rounds", type=int, default=2)
    return parser.parse_args()


def resolve_problem_path(problem_path: str) -> str:
    aliases = {
        "test": "data/dataset/test.json",
        "putnam": "data/dataset/putnam.json",
        "matharena": "data/dataset/matharena.json",
    }
    return aliases.get(problem_path, problem_path)


def model_stem(model: str) -> str:
    return Path(model).stem.replace(":", "_")


def experiment_tag(problem_path: str, conjecturer_model: str, baseline: str) -> str:
    return f"{Path(problem_path).stem}_{model_stem(conjecturer_model)}_{baseline}"


def parse_problem_names(args: argparse.Namespace) -> Any:
    if not args.enable_problem_name_filter:
        return "all"
    raw = args.problem_name_list or args.problem_name
    if raw in ("all", "remaining"):
        return raw
    return [x.strip() for x in str(raw).split(",") if x.strip()]


def load_dataset(problem_path: str) -> List[Dict[str, Any]]:
    with open(problem_path, "r", encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, list):
        raise ValueError(f"{problem_path} must contain a JSON list.")
    return data


def select_entries(data: Sequence[Dict[str, Any]], problem_name: Any) -> List[Dict[str, Any]]:
    entries = [e for e in data if e.get("is_formalized") == "True"]
    if problem_name == "all":
        return list(entries)
    if problem_name == "remaining":
        return list(entries)
    selected = set(problem_name or [])
    return [e for e in entries if e.get("name") in selected]


def read_jsonl(path: str) -> List[Dict[str, Any]]:
    if not os.path.exists(path):
        return []
    out: List[Dict[str, Any]] = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                out.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    return out


def write_jsonl(path: str, records: Iterable[Dict[str, Any]]) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        for record in records:
            f.write(json.dumps(record, ensure_ascii=False) + "\n")


def append_jsonl(path: str, record: Dict[str, Any]) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "a", encoding="utf-8") as f:
        f.write(json.dumps(record, ensure_ascii=False) + "\n")


def _answer_verifier_info(entry: Dict[str, Any]) -> Dict[str, Any]:
    info = entry.get("formal_answer_info") or {}
    out = {
        "header": ecp_preamble(entry),
        "answer_type": entry["answer_type"],
        "admissible_vocabulary": info.get("admissible_vocabulary", "[]"),
        QUANTIFIER_OPTION_KEY: _answer_quantifier_option(info),
    }
    return out


def _previous_answer_feedback(previous_round_answers: Optional[Dict[str, Dict[str, Any]]], name: str) -> str:
    if not previous_round_answers or name not in previous_round_answers:
        return ""
    prev = previous_round_answers[name]
    prev_answer = str(prev.get("proposed_answer", "")).replace("\n", " ")
    return (
        "\n\n-- [ECP feedback] Your previous answer was refuted by a proof of the negated "
        "answer-substituted theorem.\n"
        f"-- [ECP feedback] Previous answer: {prev_answer}\n"
        "-- [ECP feedback] Construct a different answer.\n"
    )


def construct_answer_for_entry(
    entry: Dict[str, Any],
    output_dir: str,
    temp_formalization_dir: str,
    baseline: str,
    conjecturer_model: str,
    previous_round_answers: Optional[Dict[str, Dict[str, Any]]] = None,
    current_round: int = 1,
) -> Dict[str, Any]:
    name = entry["name"]
    answer = "Error"
    answer_ok = False
    answer_error = ""
    history = ""
    stats = {
        "runtime_sec": 0.0,
        "output_tokens": 0,
        "tool_calls": 0,
        "api_calls": 0,
        "llm_calls": 0,
    }

    verifier_info = _answer_verifier_info(entry)
    formal_statement = full_problem_statement(entry) + _previous_answer_feedback(previous_round_answers, name)
    conjecturer = None

    try:
        os.makedirs(temp_formalization_dir, exist_ok=True)
        conjecturer = Conjecturer(
            filename=os.path.join(temp_formalization_dir, f"{name}.lean"),
            model=conjecturer_model,
            enable_mcp=(baseline == "mcp"),
        )
        answer, answer_ok = conjecturer.conjecture_answer_loop(
            formal_statement,
            verifier_checker_info=verifier_info,
            max_attempt=5,
        )
        answer_error = conjecturer.last_error
        history = conjecturer.history
        stats = conjecturer.get_answer_construction_stats()
        explanation = "answer passed Lean syntax and canonical admissibility checks" if answer_ok else answer_error

        is_equivalent = "False"
        if answer_ok and entry.get("formal_answer"):
            is_equivalent = formal_equivalence_checker(
                name=name,
                header=ecp_preamble(entry),
                answer_type=entry["answer_type"],
                answer_1=entry["formal_answer"],
                answer_2=answer,
            )

        result = {
            "name": name,
            "round": current_round,
            "actual_answer": entry.get("formal_answer", ""),
            "proposed_answer": answer,
            "answer_ok": "True" if answer_ok else "False",
            "answer_error": answer_error,
            "is_equivalent": is_equivalent,
            "explanation": explanation,
            "answer_construction_runtime_sec": stats.get("runtime_sec", 0.0),
            "answer_construction_output_tokens": stats.get("output_tokens", 0),
            "answer_construction_tool_calls": stats.get("tool_calls", 0),
            "answer_construction_api_calls": stats.get("api_calls", 0),
            "answer_construction_llm_calls": stats.get("llm_calls", 0),
        }
    except Exception as exc:
        if conjecturer is not None:
            history = getattr(conjecturer, "history", history)
            stats = conjecturer.get_answer_construction_stats()
            if answer == "Error":
                answer = getattr(conjecturer, "last_answer", answer) or answer
        result = {
            "name": name,
            "round": current_round,
            "actual_answer": entry.get("formal_answer", ""),
            "proposed_answer": answer,
            "answer_ok": "False",
            "answer_error": repr(exc),
            "is_equivalent": "False",
            "explanation": "Exception during answer construction",
            "answer_construction_runtime_sec": stats.get("runtime_sec", 0.0),
            "answer_construction_output_tokens": stats.get("output_tokens", 0),
            "answer_construction_tool_calls": stats.get("tool_calls", 0),
            "answer_construction_api_calls": stats.get("api_calls", 0),
            "answer_construction_llm_calls": stats.get("llm_calls", 0),
        }

    history_dir = os.path.join(output_dir, "llm_history", "conjecturer")
    os.makedirs(history_dir, exist_ok=True)
    with open(os.path.join(history_dir, f"{name}.txt"), "w", encoding="utf-8") as f:
        f.write(history)

    return result


def run_answer_gen(
    output_dir: str,
    problem_path: str,
    problem_name: Any,
    baseline: str,
    conjecturer_model: str,
    temp_formalization_dir: str = "Formalization/cache",
    previous_round_answers: Optional[Dict[str, Dict[str, Any]]] = None,
    current_round: int = 1,
    resume: bool = False,
) -> Dict[str, Any]:
    data = load_dataset(problem_path)
    entries = select_entries(data, problem_name)
    tag = experiment_tag(problem_path, conjecturer_model, baseline)
    answer_dir = os.path.join(output_dir, "conjecturer", tag)
    os.makedirs(answer_dir, exist_ok=True)
    temp_dir = os.path.join(temp_formalization_dir, "conjecturer", tag)
    partial_path = os.path.join(answer_dir, "partial_results.jsonl")
    summary_path = os.path.join(answer_dir, "summary.json")

    processed: List[Dict[str, Any]] = read_jsonl(partial_path) if resume else []
    processed_names = {r.get("name") for r in processed}
    pending_entries = [e for e in entries if e.get("name") not in processed_names]
    if not resume and os.path.exists(partial_path):
        os.remove(partial_path)

    print(f"[answer_gen] output={answer_dir}")
    print(f"[answer_gen] problems={len(entries)}, pending={len(pending_entries)}, resumed={len(processed)}")

    results: List[Dict[str, Any]] = list(processed)
    workers = os.cpu_count() or 1
    write_lock = threading.Lock()

    def process(entry: Dict[str, Any]) -> Dict[str, Any]:
        result = construct_answer_for_entry(
            entry=entry,
            output_dir=answer_dir,
            temp_formalization_dir=temp_dir,
            baseline=baseline,
            conjecturer_model=conjecturer_model,
            previous_round_answers=previous_round_answers,
            current_round=current_round,
        )
        with write_lock:
            append_jsonl(partial_path, result)
        return result

    if workers == 1:
        for entry in tqdm(pending_entries, desc="constructing answers"):
            results.append(process(entry))
    else:
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
            future_map = {executor.submit(process, entry): entry for entry in pending_entries}
            for future in tqdm(concurrent.futures.as_completed(future_map), total=len(future_map), desc="constructing answers"):
                results.append(future.result())

    results.sort(key=lambda r: str(r.get("name", "")))
    with open(summary_path, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2, ensure_ascii=False)

    eval_path = write_prover_eval_files(results, data, answer_dir)
    ok_count = sum(1 for r in results if is_true_value(r.get("answer_ok")))
    eq_count = sum(1 for r in results if is_true_value(r.get("is_equivalent")))
    print(f"[answer_gen] answer_ok={ok_count}/{len(results)}; equivalent_to_ground_truth={eq_count}/{len(results)}")
    return {
        "answer_dir": answer_dir,
        "summary_path": summary_path,
        "partial_path": partial_path,
        "eval_path": eval_path,
        "results": results,
        "data": data,
    }


def _valid_answer_record(record: Dict[str, Any]) -> bool:
    answer = record.get("proposed_answer")
    return (
        is_true_value(record.get("answer_ok"))
        and isinstance(answer, str)
        and answer.strip() not in {"", "Error"}
    )


def build_prover_records(
    answer_results: Sequence[Dict[str, Any]],
    data: Sequence[Dict[str, Any]],
    negated: bool = False,
    include_names: Optional[Set[str]] = None,
) -> List[Dict[str, Any]]:
    data_by_name = {e["name"]: e for e in data if "name" in e}
    records: List[Dict[str, Any]] = []
    for result in answer_results:
        name = result.get("name")
        if not name or name not in data_by_name:
            continue
        if include_names is not None and name not in include_names:
            continue
        if not _valid_answer_record(result):
            continue

        entry = data_by_name[name]
        answer = result["proposed_answer"]
        theorem = answer_substituted_theorem(entry, answer, negated=negated)
        preamble = ecp_preamble(entry)
        formal_statement = f"{preamble}\n{theorem}"
        records.append(
            {
                "name": name,
                "split": entry.get("split", "valid"),
                "informal_prefix": "",
                "formal_statement": formal_statement,
                "lean4_code": formal_statement,
                "header": entry.get("header", ""),
                "answer_type": entry.get("answer_type", ""),
                "proposed_answer": answer,
                "negated": bool(negated),
            }
        )
    return records


def write_prover_eval_files(
    answer_results: Sequence[Dict[str, Any]],
    data: Sequence[Dict[str, Any]],
    output_dir: str,
    positive_names: Optional[Set[str]] = None,
    negated_names: Optional[Set[str]] = None,
) -> str:
    os.makedirs(output_dir, exist_ok=True)
    positive_path = os.path.join(output_dir, "prover_eval_temp.jsonl")
    negated_path = os.path.join(output_dir, "prover_eval_temp_negated.jsonl")
    write_jsonl(
        positive_path,
        build_prover_records(answer_results, data, negated=False, include_names=positive_names),
    )
    write_jsonl(
        negated_path,
        build_prover_records(answer_results, data, negated=True, include_names=negated_names),
    )
    return positive_path


def build_llm_baseline_records(entries: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    records: List[Dict[str, Any]] = []
    for entry in entries:
        name = entry.get("name")
        formal_statement = full_problem_statement(entry)
        if not name or not formal_statement.strip():
            continue
        answer_info = entry.get("formal_answer_info") or {}
        record = {
            "name": name,
            "split": entry.get("split", "valid"),
            "informal_prefix": "",
            "formal_statement": formal_statement,
            "lean4_code": formal_statement,
            "header": entry.get("header", ""),
            "answer_type": entry.get("answer_type", ""),
            "answer_name": entry.get("answer_name", ""),
            "admissible_vocabulary": answer_info.get("admissible_vocabulary", "[]"),
            "theorem_name": name,
            QUANTIFIER_OPTION_KEY: _answer_quantifier_option(answer_info),
        }
        records.append(record)
    return records


def build_equality_prover_records(
    answer_results: Sequence[Dict[str, Any]],
    data: Sequence[Dict[str, Any]],
    include_names: Optional[Set[str]] = None,
) -> List[Dict[str, Any]]:
    data_by_name = {e["name"]: e for e in data if "name" in e}
    records: List[Dict[str, Any]] = []
    for result in answer_results:
        name = result.get("name")
        if not name or name not in data_by_name:
            continue
        if include_names is not None and name not in include_names:
            continue
        if is_true_value(result.get("is_equivalent")):
            continue
        if not _valid_answer_record(result):
            continue

        entry = data_by_name[name]
        actual_answer = str(entry.get("formal_answer") or result.get("actual_answer") or "").strip()
        proposed_answer = str(result.get("proposed_answer") or "").strip()
        if not actual_answer or not proposed_answer:
            continue

        answer_type = entry["answer_type"]
        formal_statement = (
            "import utils.fol\n"
            f"{ecp_preamble(entry)}\n"
            f"theorem check_equality : ({actual_answer} : {answer_type}) = "
            f"({proposed_answer} : {answer_type}) := by "
        )
        records.append(
            {
                "name": name,
                "split": entry.get("split", "valid"),
                "informal_prefix": "",
                "formal_statement": formal_statement,
                "lean4_code": formal_statement,
                "header": entry.get("header", ""),
                "answer_type": answer_type,
                "actual_answer": actual_answer,
                "proposed_answer": proposed_answer,
                "equality_check": True,
            }
        )
    return records


def _write_answer_result_files(answer_dir: str, answer_results: Sequence[Dict[str, Any]]) -> None:
    rows = sorted((dict(r) for r in answer_results), key=lambda r: str(r.get("name", "")))
    write_jsonl(os.path.join(answer_dir, "partial_results.jsonl"), rows)
    with open(os.path.join(answer_dir, "summary.json"), "w", encoding="utf-8") as f:
        json.dump(rows, f, indent=2, ensure_ascii=False)


def run_enhanced_equivalence_phase(
    problem_path: str,
    answer_results: Sequence[Dict[str, Any]],
    data: Sequence[Dict[str, Any]],
    answer_dir: str,
    round_dir: str,
    prover_model: str,
    pass_at_n: int,
    correction_rounds: int,
    gpu: int,
    cpu: int,
    nodes: int,
    max_model_len: int,
    run_tag: str,
) -> List[Dict[str, Any]]:
    records = build_equality_prover_records(answer_results, data)
    eval_path = os.path.join(answer_dir, "equality_eval_temp.jsonl")
    write_jsonl(eval_path, records)

    if not records:
        _write_answer_result_files(answer_dir, answer_results)
        return [dict(r) for r in answer_results]

    print(f"[equivalence] prover equality checks={len(records)}, pass@{pass_at_n}")
    proof_info = run_proof_gen(
        problem_path=problem_path,
        prover_model=prover_model,
        output_dir=round_dir,
        eval_file_path=eval_path,
        pass_at_n=pass_at_n,
        correction_samples=1,
        correction_rounds=correction_rounds,
        gpu=gpu,
        cpu=cpu,
        nodes=nodes,
        negated=False,
        max_model_len=max_model_len,
        run_tag=f"{run_tag}_equality",
    )
    solved_map = read_final_summary(proof_info["summary_path"])
    proof_bodies = load_successful_proof_bodies(proof_info["output_dir"])

    updated: List[Dict[str, Any]] = []
    changed = 0
    for result in answer_results:
        row = dict(result)
        name = str(row.get("name", ""))
        if solved_map.get(name, False):
            row["is_equivalent"] = "True"
            row["explanation"] = proof_bodies.get(name) or "proved by enhanced equality prover"
            changed += 1
        updated.append(row)

    _write_answer_result_files(answer_dir, updated)
    if changed:
        print(f"[equivalence] upgraded {changed} answer(s) to is_equivalent=True")
    else:
        print("[equivalence] no additional equalities proved")
    return updated


def _symbolic_prove_records(records: Sequence[Dict[str, Any]], output_dir: str) -> None:
    summary = []
    compilation = []
    for record in tqdm(records, desc="symbolic prover"):
        proof_body = "try_solvers"
        code = f"{record['formal_statement']}{proof_body}"
        result_text = run_lean_code(f"import utils.fol\n{code}")
        solved = "True" if "True" in str(result_text) and "error:" not in str(result_text) else "False"
        summary.append({"name": record["name"], "is_solved": solved})
        compilation.append(
            {
                "name": record["name"],
                "code": code,
                "compilation_result": {
                    "pass": solved == "True",
                    "complete": solved == "True",
                    "system_errors": None if solved == "True" else str(result_text),
                },
            }
        )
    os.makedirs(os.path.join(output_dir, "final_summary"), exist_ok=True)
    with open(os.path.join(output_dir, "final_summary", "final_summary.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2, ensure_ascii=False)
    with open(os.path.join(output_dir, "code_compilation_repl.json"), "w", encoding="utf-8") as f:
        json.dump(compilation, f, indent=2, ensure_ascii=False)


def run_proof_gen(
    problem_path: str,
    prover_model: str,
    output_dir: str,
    gpu: int,
    cpu: int,
    eval_file_path: str = "",
    pass_at_n: int = 16,
    correction_samples: int = 1,
    correction_rounds: int = 2,
    nodes: int = 1,
    negated: bool = False,
    max_model_len: int = DEFAULT_PROVER_MAX_MODEL_LEN,
    baseline: str = "",
    conjecturer_model: str = "",
    run_tag: str = "",
    enable_witness_admissibility_check: bool = False,
) -> Dict[str, str]:
    stem = Path(problem_path).stem
    if not eval_file_path:
        if not conjecturer_model or not baseline:
            raise ValueError("Provide eval_file_path, or provide conjecturer_model and baseline for legacy lookup.")
        tag = experiment_tag(problem_path, conjecturer_model, baseline)
        filename = "prover_eval_temp_negated.jsonl" if negated else "prover_eval_temp.jsonl"
        eval_file_path = os.path.join(output_dir, "conjecturer", tag, filename)

    if not os.path.exists(eval_file_path):
        raise FileNotFoundError(f"eval_file_path not found: {eval_file_path}")

    tag = run_tag or (experiment_tag(problem_path, conjecturer_model, baseline) if conjecturer_model else stem)
    if negated and not tag.endswith("_negated"):
        tag = f"{tag}_negated"
    final_output_dir = os.path.join(output_dir, "prover", tag, model_stem(prover_model))
    os.makedirs(final_output_dir, exist_ok=True)

    records = read_jsonl(eval_file_path)
    if not records:
        os.makedirs(os.path.join(final_output_dir, "final_summary"), exist_ok=True)
        with open(os.path.join(final_output_dir, "final_summary", "final_summary.json"), "w", encoding="utf-8") as f:
            json.dump([], f, indent=2, ensure_ascii=False)
        with open(os.path.join(final_output_dir, "code_compilation_repl.json"), "w", encoding="utf-8") as f:
            json.dump([], f, indent=2, ensure_ascii=False)
        print(f"[proof_gen] no prover records in {eval_file_path}; wrote empty summary")
    elif prover_model == "symbolic":
        _symbolic_prove_records(records, final_output_dir)
    else:
        commercial_parallel = os.environ.get("COMMERCIAL_PARALLEL", "").strip() or str(cpu)
        cmd = [
            "bash", "src/goedel/pipeline.sh",
            "-m", str(prover_model),
            "-M", str(max_model_len),
            "-d", str(eval_file_path),
            "-o", str(final_output_dir),
            "-g", str(gpu),
            "-N", str(nodes),
            "-c", str(cpu),
            "-P", commercial_parallel,
            "-i", str(pass_at_n),
            "-r", str(correction_samples),
            "-R", str(correction_rounds),
        ]
        if enable_witness_admissibility_check:
            cmd.append("-a")
        subprocess.run(cmd, check=True)

    return {
        "output_dir": final_output_dir,
        "summary_path": os.path.join(final_output_dir, "final_summary", "final_summary.json"),
        "eval_file_path": eval_file_path,
    }


def final_prover_output_dir(
    problem_path: str,
    output_dir: str,
    prover_model: str,
    run_tag: str,
    negated: bool = False,
) -> str:
    stem = Path(problem_path).stem
    tag = run_tag or stem
    if negated and not tag.endswith("_negated"):
        tag = f"{tag}_negated"
    return os.path.join(output_dir, "prover", tag, model_stem(prover_model))


def read_final_summary(path: str) -> Dict[str, bool]:
    if not os.path.exists(path):
        return {}
    with open(path, "r", encoding="utf-8") as f:
        rows = json.load(f)
    return {str(row.get("name")): is_true_value(row.get("is_solved")) for row in rows if row.get("name")}


def _origin_from_generation_id(problem_id: str) -> str:
    text = str(problem_id)
    match = re.match(r"^(?P<origin>.+?)_g\d+(?:_corr\d+_g\d+)*$", text)
    if match:
        return match.group("origin")
    return text


def load_successful_proof_bodies(prover_output_dir: str) -> Dict[str, str]:
    bodies: Dict[str, str] = {}
    compile_paths = sorted(Path(prover_output_dir).glob("code_compilation_repl*.json"))
    for path in compile_paths:
        try:
            with open(path, "r", encoding="utf-8") as f:
                rows = json.load(f)
        except Exception:
            continue
        if not isinstance(rows, list):
            continue
        for row in rows:
            comp = row.get("compilation_result") or {}
            if not (comp.get("complete") and comp.get("pass", True)):
                continue
            origin = _origin_from_generation_id(str(row.get("name", "")))
            code = row.get("code") or row.get("full_code") or ""
            body = extract_proof_body(code)
            if origin and body and origin not in bodies:
                bodies[origin] = body
    return bodies


def load_successful_full_proofs(prover_output_dir: str) -> Dict[str, Dict[str, str]]:
    proofs: Dict[str, Dict[str, str]] = {}
    output_path = Path(prover_output_dir)
    compile_paths = sorted(output_path.glob("code_compilation_repl*.json"))
    for compile_path in compile_paths:
        match = re.match(r"code_compilation_repl(?P<suffix>.*)\.json$", compile_path.name)
        suffix = match.group("suffix") if match else ""
        inference_path = output_path / f"to_inference_codes{suffix}.json"
        full_code_by_id: Dict[str, str] = {}
        if inference_path.exists():
            try:
                with open(inference_path, "r", encoding="utf-8") as f:
                    generated_rows = json.load(f)
            except Exception:
                generated_rows = []
            if isinstance(generated_rows, list):
                full_code_by_id = {
                    str(row.get("problem_id")): str(row.get("full_code") or "")
                    for row in generated_rows
                    if isinstance(row, dict) and row.get("problem_id")
                }

        try:
            with open(compile_path, "r", encoding="utf-8") as f:
                compile_rows = json.load(f)
        except Exception:
            continue
        if not isinstance(compile_rows, list):
            continue

        for row in compile_rows:
            if not isinstance(row, dict):
                continue
            comp = row.get("compilation_result") or {}
            if not (comp.get("complete") and comp.get("pass", True)):
                continue
            generation_id = str(row.get("name", ""))
            origin = _origin_from_generation_id(generation_id)
            proof = full_code_by_id.get(generation_id) or str(row.get("code") or row.get("full_code") or "")
            if origin and proof and origin not in proofs:
                proofs[origin] = {
                    "name": origin,
                    "generation_id": generation_id,
                    "proof_valid": "True",
                    "proof": proof,
                }
    return proofs


def assemble_successful_proofs(
    answer_results: Sequence[Dict[str, Any]],
    data: Sequence[Dict[str, Any]],
    solved_map: Dict[str, bool],
    prover_output_dir: str,
    output_dir: str,
) -> List[Dict[str, Any]]:
    return assemble_successful_proofs_from_bodies(
        answer_results=answer_results,
        data=data,
        solved_map=solved_map,
        proof_bodies=load_successful_proof_bodies(prover_output_dir),
        output_dir=output_dir,
    )


def assemble_successful_proofs_from_bodies(
    answer_results: Sequence[Dict[str, Any]],
    data: Sequence[Dict[str, Any]],
    solved_map: Dict[str, bool],
    proof_bodies: Dict[str, str],
    output_dir: str,
    proof_sources: Optional[Dict[str, str]] = None,
) -> List[Dict[str, Any]]:
    data_by_name = {e["name"]: e for e in data if "name" in e}
    answers_by_name = {r["name"]: r for r in answer_results if r.get("name")}
    assembled: List[Dict[str, Any]] = []

    for name, solved in solved_map.items():
        if not solved or name not in data_by_name or name not in answers_by_name:
            continue
        body = proof_bodies.get(name, "")
        if not body:
            continue
        entry = data_by_name[name]
        answer = answers_by_name[name]["proposed_answer"]
        lean_code = assemble_existential_proof(entry, answer, body)
        source = (proof_sources or {}).get(name, "goedel_final_summary")
        assembled.append(
            {
                "name": name,
                "proposed_answer": answer,
                "assembled_proof_valid": "True",
                "assembled_proof": lean_code,
                "assembly_verifier_output": "",
                "assembled_proof_valid_source": source,
            }
        )

    os.makedirs(output_dir, exist_ok=True)
    path = os.path.join(output_dir, "successful_proofs.jsonl")
    write_jsonl(path, assembled)
    return assembled


def _automation_row_origin(row: Dict[str, Any]) -> str:
    raw_name = row.get("origin_problem_id") or row.get("name") or row.get("problem_id")
    return _origin_from_generation_id(str(raw_name or ""))


def _load_automation_compilation_rows(output_path: str) -> List[Dict[str, Any]]:
    if not os.path.exists(output_path):
        return []

    try:
        with open(output_path, "r", encoding="utf-8") as f:
            rows = json.load(f)
    except Exception as exc:
        print(
            f"[automation] existing fallback compilation output could not be read "
            f"({output_path}): {exc}; rerunning requested fallback rows",
            flush=True,
        )
        return []

    if not isinstance(rows, list):
        print(
            f"[automation] existing fallback compilation output is not a JSON list "
            f"({output_path}); rerunning requested fallback rows",
            flush=True,
        )
        return []

    return [row for row in rows if isinstance(row, dict)]


def _read_json_list(path: str) -> List[Dict[str, Any]]:
    if not os.path.exists(path):
        return []
    try:
        with open(path, "r", encoding="utf-8") as f:
            rows = json.load(f)
    except Exception:
        return []
    if not isinstance(rows, list):
        return []
    return [row for row in rows if isinstance(row, dict)]


def _write_json_list(path: str, rows: Sequence[Dict[str, Any]]) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(list(rows), f, indent=2, ensure_ascii=False)


def _upsert_json_rows_by_problem_id(path: str, rows: Sequence[Dict[str, Any]]) -> None:
    replacement_by_id = {
        str(row.get("problem_id")): dict(row)
        for row in rows
        if row.get("problem_id") is not None
    }
    if not replacement_by_id:
        return
    existing = _read_json_list(path)
    merged = [
        row for row in existing
        if str(row.get("problem_id")) not in replacement_by_id
    ]
    merged.extend(replacement_by_id[key] for key in sorted(replacement_by_id))
    _write_json_list(path, merged)


def _automation_sample_id(problem_name: str, sample_idx: int) -> str:
    return f"{problem_name}_g{sample_idx}"


def _automation_full_code(row: Dict[str, Any]) -> str:
    return str(row.get("code") or row.get("full_code") or "")


def preseed_automation_successes_for_prover(
    prover_output_dir: str,
    eval_records: Sequence[Dict[str, Any]],
    automation_success_rows: Dict[str, Dict[str, Any]],
    pass_at_n: int,
) -> None:
    if not automation_success_rows:
        return

    eval_by_name = {str(row.get("name")): row for row in eval_records if row.get("name")}
    full_records: List[Dict[str, Any]] = []
    inference_codes: List[Dict[str, Any]] = []
    compilation_rows: List[Dict[str, Any]] = []
    sample_count = max(1, int(pass_at_n))

    for name in sorted(automation_success_rows):
        automation_row = automation_success_rows[name]
        full_code = _automation_full_code(automation_row)
        if not full_code:
            continue
        base = dict(eval_by_name.get(name, {}))
        compilation_result = dict(automation_row.get("compilation_result") or {})
        proof_body = extract_proof_body(full_code)

        for sample_idx in range(sample_count):
            problem_id = _automation_sample_id(name, sample_idx)
            id_maps = [{"origin_problem_id": name}, {"generation_id": problem_id}]
            record = dict(base)
            record.update(
                {
                    "name": name,
                    "problem_id": problem_id,
                    "origin_problem_id": name,
                    "id_maps": id_maps,
                    "model_output": proof_body or "proved by automation fallback",
                    "full_code": full_code,
                    "automation_fallback_preseeded": True,
                }
            )
            inference_record = {
                "problem_id": problem_id,
                "origin_problem_id": name,
                "id_maps": id_maps,
                "formal_statement": record.get("formal_statement", ""),
                "model_input": record.get("model_input", ""),
                "messages_history_list": record.get("messages_history_for_this_attempt", []),
                "model_output": record["model_output"],
                "full_code": full_code,
                "automation_fallback_preseeded": True,
            }
            compilation_row = dict(automation_row)
            compilation_row.update(
                {
                    "name": problem_id,
                    "problem_id": problem_id,
                    "origin_problem_id": name,
                    "code": full_code,
                    "full_code": full_code,
                    "compilation_result": dict(compilation_result),
                    "automation_fallback_preseeded": True,
                }
            )
            full_records.append(record)
            inference_codes.append(inference_record)
            compilation_rows.append(compilation_row)

    if not full_records:
        return

    os.makedirs(prover_output_dir, exist_ok=True)
    _upsert_json_rows_by_problem_id(os.path.join(prover_output_dir, "full_records.json"), full_records)
    _upsert_json_rows_by_problem_id(os.path.join(prover_output_dir, "to_inference_codes.json"), inference_codes)
    _upsert_json_rows_by_problem_id(os.path.join(prover_output_dir, "code_compilation_repl.json"), compilation_rows)
    print(
        f"[automation] preseeded {len(automation_success_rows)} automation-solved problem(s) "
        f"as {len(full_records)} prover sample(s) in {prover_output_dir}",
        flush=True,
    )


def run_final_automation_fallback(
    final_eval_path: str,
    failed_names: Set[str],
    output_dir: str,
    cpu: int,
    nodes: int,
) -> Tuple[Dict[str, bool], Dict[str, str], Dict[str, Dict[str, Any]]]:
    if not failed_names:
        return {}, {}, {}

    final_records = read_jsonl(final_eval_path)
    records: List[Dict[str, Any]] = []
    for row in final_records:
        name = str(row.get("name", ""))
        if name not in failed_names:
            continue
        record = dict(row)
        record.setdefault("origin_problem_id", name)
        records.append(record)

    if not records:
        return {}, {}, {}

    automation_dir = os.path.join(output_dir, "automation_fallback")
    os.makedirs(automation_dir, exist_ok=True)
    input_path = os.path.join(automation_dir, "automation_input.json")
    output_path = os.path.join(automation_dir, "code_compilation_repl.json")

    with open(input_path, "w", encoding="utf-8") as f:
        json.dump(records, f, indent=2, ensure_ascii=False)

    existing_rows = _load_automation_compilation_rows(output_path)
    existing_names = {
        _automation_row_origin(row)
        for row in existing_rows
        if isinstance(row.get("compilation_result"), dict)
    }
    missing_names = set(failed_names) - existing_names

    if missing_names:
        rows_to_compile = [
            record for record in records
            if str(record.get("name", "")) in missing_names
        ]
        compile_input_path = input_path
        compile_output_path = output_path
        if existing_rows:
            compile_input_path = os.path.join(automation_dir, "automation_input_missing.json")
            compile_output_path = os.path.join(automation_dir, "code_compilation_repl_missing.json")
            with open(compile_input_path, "w", encoding="utf-8") as f:
                json.dump(rows_to_compile, f, indent=2, ensure_ascii=False)

        cmd = [
            sys.executable,
            "-m",
            "src.goedel.compile",
            "--input_path",
            compile_input_path,
            "--output_path",
            compile_output_path,
            "--cpu",
            str(max(1, min(int(cpu), len(rows_to_compile)))),
            "--node",
            str(max(1, int(nodes))),
            "--enable_automation_tactics",
        ]
        if existing_rows:
            print(
                f"[automation] reusing {len(existing_names & failed_names)}/{len(failed_names)} "
                f"existing fallback compilation row(s); compiling {len(rows_to_compile)} missing row(s)",
                flush=True,
            )
        print(f"[automation] attempting {len(rows_to_compile)} failed final proof(s) with fixed tactic portfolio", flush=True)
        subprocess.run(cmd, check=True)

        try:
            with open(compile_output_path, "r", encoding="utf-8") as f:
                new_rows = json.load(f)
        except Exception:
            new_rows = []
        if not isinstance(new_rows, list):
            new_rows = []

        new_names = {
            _automation_row_origin(row)
            for row in new_rows
            if isinstance(row, dict)
        }
        rows = [
            row for row in existing_rows
            if _automation_row_origin(row) not in new_names
        ] + [row for row in new_rows if isinstance(row, dict)]
        with open(output_path, "w", encoding="utf-8") as f:
            json.dump(rows, f, indent=2, ensure_ascii=False)
    else:
        rows = existing_rows
        print(
            f"[automation] reusing existing fallback compilation output for "
            f"{len(failed_names)} failed final proof(s): {output_path}",
            flush=True,
        )

    solved_map: Dict[str, bool] = {}
    proof_bodies: Dict[str, str] = {}
    successful_rows: Dict[str, Dict[str, Any]] = {}
    if not isinstance(rows, list):
        rows = []

    for row in rows:
        if not isinstance(row, dict):
            continue
        name = _automation_row_origin(row)
        if name not in failed_names:
            continue
        comp = row.get("compilation_result") or {}
        solved = bool(comp.get("complete") and comp.get("pass", True))
        solved_map[name] = solved
        if solved:
            body = extract_proof_body(str(row.get("code") or row.get("full_code") or ""))
            if body:
                proof_bodies[name] = body
                successful_rows[name] = dict(row)

    solved_count = sum(1 for solved in solved_map.values() if solved)
    print(f"[automation] solved {solved_count}/{len(records)} failed final proof(s)", flush=True)
    return solved_map, proof_bodies, successful_rows


def run_llm_baseline(
    problem_path: str,
    problem_name: Any,
    base_output_dir: str,
    prover_model: str,
    num_cpu: int,
    gpu: int,
    nodes: int,
    pass_at_n: int,
    correction_rounds: int,
    max_model_len: int = DEFAULT_PROVER_MAX_MODEL_LEN,
) -> Dict[str, Any]:
    data = load_dataset(problem_path)
    selected_entries = select_entries(data, problem_name)
    stem = Path(problem_path).stem
    root = os.path.join(
        base_output_dir,
        f"{stem}_llm_baseline_{model_stem(prover_model)}",
    )
    os.makedirs(root, exist_ok=True)

    eval_path = os.path.join(root, "llm_baseline_eval.jsonl")
    records = build_llm_baseline_records(selected_entries)
    write_jsonl(eval_path, records)
    print(f"[llm_baseline] output={root}")
    print(f"[llm_baseline] prover records={len(records)}")

    proof_info = run_proof_gen(
        problem_path=problem_path,
        prover_model=prover_model,
        output_dir=root,
        eval_file_path=eval_path,
        pass_at_n=pass_at_n,
        correction_samples=1,
        correction_rounds=correction_rounds,
        gpu=gpu,
        cpu=num_cpu,
        nodes=nodes,
        negated=False,
        max_model_len=max_model_len,
        run_tag="llm_baseline",
        enable_witness_admissibility_check=True,
    )

    solved_map = read_final_summary(proof_info["summary_path"])
    successful_proofs_by_name = load_successful_full_proofs(proof_info["output_dir"])
    successful_proofs_path = os.path.join(root, "successful_proofs.jsonl")
    write_jsonl(
        successful_proofs_path,
        [successful_proofs_by_name[name] for name in sorted(successful_proofs_by_name)],
    )

    summary = [
        {
            "name": entry["name"],
            "proof_generation_attempted": "True",
            "prover_solved": "True" if solved_map.get(entry["name"], False) else "False",
            "proof_valid": "True" if entry["name"] in successful_proofs_by_name else "False",
        }
        for entry in selected_entries
    ]
    solved_count = sum(1 for row in summary if is_true_value(row.get("prover_solved")))
    total = len(selected_entries)
    accuracy = solved_count / total if total else 0.0
    out = {
        "problem_path": problem_path,
        "mode": "llm_baseline",
        "prover_model": prover_model,
        "pass_at_n": pass_at_n,
        "correction_rounds": correction_rounds,
        "total": total,
        "solved": solved_count,
        "accuracy": accuracy,
        "eval_path": eval_path,
        "proof_output_dir": proof_info["output_dir"],
        "proof_summary_path": proof_info["summary_path"],
        "successful_proofs_path": successful_proofs_path,
        "summary": summary,
    }
    summary_path = os.path.join(root, "llm_baseline_summary.json")
    with open(summary_path, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, ensure_ascii=False)
    print(f"[llm_baseline] accuracy={solved_count}/{total} = {accuracy:.2%}")
    print(f"[llm_baseline] wrote {summary_path}")
    return out


def run_ecp_multi_round(
    problem_path: str,
    problem_name: Any,
    base_output_dir: str,
    baseline: str,
    conjecturer_model: str,
    prover_model: str,
    temp_formalization_dir: str,
    num_cpu: int,
    gpu: int,
    nodes: int,
    pass_at_n: int,
    correction_rounds: int,
    equivalence_prover_model: str = "Goedel-LM/Goedel-Prover-V2-8B",
    equivalence_pass_at_n: int = 4,
    equivalence_correction_rounds: int = 2,
    max_rounds: int = 2,
    max_model_len: int = DEFAULT_PROVER_MAX_MODEL_LEN,
    enable_enhanced_equivalence: bool = True,
    enable_negated_proof: bool = True,
    enable_final_automation: bool = True,
    resume: bool = False,
) -> Dict[str, Any]:
    data = load_dataset(problem_path)
    selected_entries = select_entries(data, problem_name)
    selected_names = {e["name"] for e in selected_entries}
    stem = Path(problem_path).stem
    root = os.path.join(
        base_output_dir,
        f"{stem}_{model_stem(conjecturer_model)}_{baseline}_{model_stem(prover_model)}",
    )
    os.makedirs(root, exist_ok=True)

    final_by_name: Dict[str, Dict[str, Any]] = {}
    finalized_answers_by_name: Dict[str, Dict[str, Any]] = {}
    previous_round_answers: Dict[str, Dict[str, Any]] = {}
    retry_names: Set[str] = set(selected_names)
    proof_pending_names: Set[str] = set()
    solved_map: Dict[str, bool] = {}
    negated_solved_map: Dict[str, bool] = {}
    automation_solved_map: Dict[str, bool] = {}
    assembled_by_name: Dict[str, Dict[str, Any]] = {}
    tag = experiment_tag(problem_path, conjecturer_model, baseline)
    proof_cycle = 0
    max_answer_rounds = max(1, max_rounds)

    for round_idx in range(1, max_answer_rounds + 1):
        if not retry_names:
            break

        current_problem_name: Any = sorted(retry_names)
        if round_idx > 1 and not enable_negated_proof:
            break

        round_dir = os.path.join(root, f"round_{round_idx}")
        print(f"[ECP] round {round_idx}: {len(current_problem_name)} problem(s)")
        answer_info = run_answer_gen(
            output_dir=round_dir,
            problem_path=problem_path,
            problem_name=current_problem_name,
            baseline=baseline,
            conjecturer_model=conjecturer_model,
            temp_formalization_dir=temp_formalization_dir,
            previous_round_answers=previous_round_answers or None,
            current_round=round_idx,
            resume=resume,
        )
        answer_results = answer_info["results"]
        answer_dir = answer_info["answer_dir"]

        if enable_enhanced_equivalence:
            answer_results = run_enhanced_equivalence_phase(
                problem_path=problem_path,
                answer_results=answer_results,
                data=data,
                answer_dir=answer_dir,
                round_dir=round_dir,
                prover_model=equivalence_prover_model,
                pass_at_n=equivalence_pass_at_n,
                correction_rounds=equivalence_correction_rounds,
                gpu=gpu,
                cpu=num_cpu,
                nodes=nodes,
                max_model_len=max_model_len,
                run_tag=tag,
            )

        answer_by_name = {r["name"]: r for r in answer_results if r.get("name")}
        for name in current_problem_name:
            if name in answer_by_name:
                answer_record = dict(answer_by_name[name])
                finalized_answers_by_name[name] = answer_record
                if _valid_answer_record(answer_record):
                    proof_pending_names.add(name)
                else:
                    proof_pending_names.discard(name)
                solved_map.pop(name, None)
                automation_solved_map.pop(name, None)
                assembled_by_name.pop(name, None)

        pre_final_refutation_names = {
            name
            for name in current_problem_name
            if _valid_answer_record(answer_by_name.get(name, {}))
            and not is_true_value(answer_by_name.get(name, {}).get("is_equivalent"))
        }
        round_negated_solved_map: Dict[str, bool] = {}
        refuted_names: Set[str] = set()
        if enable_negated_proof and pre_final_refutation_names:
            write_prover_eval_files(
                answer_results,
                data,
                answer_dir,
                positive_names=set(),
                negated_names=pre_final_refutation_names,
            )
            neg_eval = os.path.join(answer_dir, "prover_eval_temp_negated.jsonl")
            if read_jsonl(neg_eval):
                neg_info = run_proof_gen(
                    problem_path=problem_path,
                    prover_model=equivalence_prover_model,
                    output_dir=round_dir,
                    eval_file_path=neg_eval,
                    pass_at_n=equivalence_pass_at_n,
                    correction_samples=1,
                    correction_rounds=equivalence_correction_rounds,
                    gpu=gpu,
                    cpu=num_cpu,
                    nodes=nodes,
                    negated=True,
                    max_model_len=max_model_len,
                    run_tag=f"{tag}_answer_refutation",
                )
                round_negated_solved_map = read_final_summary(neg_info["summary_path"])
                negated_solved_map.update(round_negated_solved_map)
                refuted_names = {n for n, solved in round_negated_solved_map.items() if solved}

        if refuted_names:
            proof_pending_names.difference_update(refuted_names)

        for name in current_problem_name:
            record = dict(final_by_name.get(name, {"name": name, "rounds": []}))
            ans = answer_by_name.get(name, {})
            round_record = {
                "round": round_idx,
                "proposed_answer": ans.get("proposed_answer", ""),
                "answer_ok": ans.get("answer_ok", "False"),
                "is_equivalent": ans.get("is_equivalent", "False"),
                "pre_final_negated_solved": "True" if round_negated_solved_map.get(name, False) else "False",
                "final_proof_attempted": "False",
                "prover_solved": "False",
                "automation_solved": "False",
                "negated_solved": "True" if negated_solved_map.get(name, False) else "False",
                "assembled_proof_valid": "False",
            }
            record["rounds"].append(round_record)
            record["proposed_answer"] = round_record["proposed_answer"]
            record["answer_ok"] = round_record["answer_ok"]
            record["is_equivalent"] = round_record["is_equivalent"]
            record["final_proof_attempted"] = "False"
            record["prover_solved"] = "True" if solved_map.get(name, False) else "False"
            record["automation_solved"] = "True" if automation_solved_map.get(name, False) else "False"
            record["negated_solved"] = round_record["negated_solved"]
            record["assembled_proof_valid"] = "True" if name in assembled_by_name else "False"
            final_by_name[name] = record

        if refuted_names and round_idx < max_answer_rounds:
            previous_round_answers = {
                name: {"proposed_answer": answer_by_name.get(name, {}).get("proposed_answer", ""), "round": round_idx}
                for name in refuted_names
            }
            retry_names = refuted_names
            print(f"[ECP] round {round_idx}: {len(refuted_names)} answer(s) refuted before final proof; reconstructing next")
            continue

        if refuted_names:
            print(f"[ECP] round {round_idx}: {len(refuted_names)} answer(s) refuted, but max_rounds={max_answer_rounds} is exhausted")

        retry_names = set()

        # Final proof generation starts only after the pre-final refutation checks
        # have either passed or exhausted the answer reconstruction budget.
        while proof_pending_names:
            proof_cycle += 1
            current_proof_names = set(proof_pending_names)
            finalized_answer_results = [
                finalized_answers_by_name[name]
                for name in sorted(selected_names)
                if name in finalized_answers_by_name
            ]
            final_answer_dir = os.path.join(root, "finalized_answers")
            _write_answer_result_files(final_answer_dir, finalized_answer_results)
            final_eval = write_prover_eval_files(
                finalized_answer_results,
                data,
                final_answer_dir,
                positive_names=current_proof_names,
                negated_names=set(),
            )

            final_proof_dir = os.path.join(root, f"final_proof_{proof_cycle}")
            final_run_tag = f"{tag}_final_{proof_cycle}"
            current_solved_map: Dict[str, bool] = {}
            proof_bodies: Dict[str, str] = {}
            proof_body_sources: Dict[str, str] = {}
            final_records = read_jsonl(final_eval)
            automation_successes: Set[str] = set()
            automation_bodies: Dict[str, str] = {}
            automation_success_rows: Dict[str, Dict[str, Any]] = {}

            if enable_final_automation:
                automation_results, automation_bodies, automation_success_rows = run_final_automation_fallback(
                    final_eval_path=final_eval,
                    failed_names=current_proof_names,
                    output_dir=final_proof_dir,
                    cpu=num_cpu,
                    nodes=nodes,
                )
                automation_successes = {
                    name for name, solved in automation_results.items()
                    if solved and name in automation_bodies
                }
                for name in automation_successes:
                    current_solved_map[name] = True
                    automation_solved_map[name] = True
                proof_bodies.update(automation_bodies)
                proof_body_sources.update(
                    {name: "automation_fallback" for name in automation_bodies}
                )

            fresh_proof_names = current_proof_names - automation_successes

            print(
                f"[ECP] final proof cycle {proof_cycle}: {len(current_proof_names)} problem(s), "
                f"automation_solved={len(automation_successes)}, fresh={len(fresh_proof_names)}"
            )

            if current_proof_names:
                fresh_eval = os.path.join(final_proof_dir, "prover_eval_temp.jsonl")
                write_jsonl(
                    fresh_eval,
                    [r for r in final_records if str(r.get("name")) in current_proof_names],
                )
                prover_output_dir = final_prover_output_dir(
                    problem_path=problem_path,
                    output_dir=final_proof_dir,
                    prover_model=prover_model,
                    run_tag=final_run_tag,
                    negated=False,
                )
                preseed_automation_successes_for_prover(
                    prover_output_dir=prover_output_dir,
                    eval_records=final_records,
                    automation_success_rows={
                        name: automation_success_rows[name]
                        for name in automation_successes
                        if name in automation_success_rows
                    },
                    pass_at_n=pass_at_n,
                )
                proof_info = run_proof_gen(
                    problem_path=problem_path,
                    prover_model=prover_model,
                    output_dir=final_proof_dir,
                    eval_file_path=fresh_eval,
                    pass_at_n=pass_at_n,
                    correction_samples=1,
                    correction_rounds=correction_rounds,
                    gpu=gpu,
                    cpu=num_cpu,
                    nodes=nodes,
                    negated=False,
                    max_model_len=max_model_len,
                    run_tag=final_run_tag,
                )
                fresh_solved_map = read_final_summary(proof_info["summary_path"])
                for name in current_proof_names:
                    current_solved_map[name] = (
                        current_solved_map.get(name, False)
                        or fresh_solved_map.get(name, False)
                    )
                fresh_proof_bodies = load_successful_proof_bodies(proof_info["output_dir"])
                proof_bodies.update(
                    {
                        name: body
                        for name, body in fresh_proof_bodies.items()
                        if name not in automation_successes
                    }
                )
                proof_body_sources.update(
                    {
                        name: "goedel_final_summary"
                        for name in fresh_proof_bodies
                        if name not in automation_successes
                    }
                )
                proof_bodies.update(automation_bodies if enable_final_automation else {})
                proof_body_sources.update(
                    {name: "automation_fallback" for name in automation_successes}
                )

            current_solved_map = {
                name: current_solved_map.get(name, False)
                for name in current_proof_names
            }

            solved_map.update(current_solved_map)
            assembled = assemble_successful_proofs_from_bodies(
                answer_results=finalized_answer_results,
                data=data,
                solved_map=current_solved_map,
                proof_bodies=proof_bodies,
                output_dir=final_proof_dir,
                proof_sources=proof_body_sources,
            )
            assembled_names = {str(row.get("name")) for row in assembled}
            missing_assembled = sorted(
                name for name, solved in current_solved_map.items()
                if solved and name not in assembled_names
            )
            if missing_assembled:
                raise RuntimeError(
                    "Goedel final_summary marked problem(s) solved, but no proof body "
                    f"could be extracted for assembly: {missing_assembled}"
                )
            for row in assembled:
                if is_true_value(row.get("assembled_proof_valid")):
                    assembled_by_name[row["name"]] = row

            proof_pending_names.difference_update(current_proof_names)

            for name in current_proof_names:
                record = dict(final_by_name.get(name, {"name": name, "rounds": []}))
                record["final_proof_attempted"] = "True"
                record["prover_solved"] = "True" if solved_map.get(name, False) else "False"
                record["automation_solved"] = "True" if automation_solved_map.get(name, False) else "False"
                record["negated_solved"] = "True" if negated_solved_map.get(name, False) else "False"
                record["assembled_proof_valid"] = "True" if name in assembled_by_name else "False"
                final_by_name[name] = record

        if retry_names:
            continue
        break

    summary = sorted(final_by_name.values(), key=lambda r: str(r.get("name", "")))
    combined_proofs_path = os.path.join(root, "successful_proofs.jsonl")
    write_jsonl(combined_proofs_path, [assembled_by_name[name] for name in sorted(assembled_by_name)])
    solved_count = sum(1 for r in summary if is_true_value(r.get("prover_solved")))
    total = len(selected_entries)
    accuracy = solved_count / total if total else 0.0
    out = {
        "problem_path": problem_path,
        "total": total,
        "solved": solved_count,
        "accuracy": accuracy,
        "enable_final_automation": enable_final_automation,
        "successful_proofs_path": combined_proofs_path,
        "summary": summary,
    }
    summary_path = os.path.join(root, "ecp_summary.json")
    with open(summary_path, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, ensure_ascii=False)
    print(f"[ECP] accuracy={solved_count}/{total} = {accuracy:.2%}")
    print(f"[ECP] wrote {summary_path}")
    return out


def main() -> None:
    args = parse_args()
    problem_path = resolve_problem_path(args.problem_path)
    cpu = args.cpu if int(args.cpu) > 0 else (os.cpu_count() or 1)
    auto_set_cuda_visible_devices()

    problem_name = parse_problem_names(args)
    if args.mode == "answer_gen":
        run_answer_gen(
            output_dir=args.output_dir,
            problem_path=problem_path,
            problem_name=problem_name,
            baseline=args.baseline,
            conjecturer_model=args.conjecturer_model,
            temp_formalization_dir=args.temp_formalization_dir,
            resume=args.resume,
        )
    elif args.mode == "proof_gen":
        run_proof_gen(
            problem_path=problem_path,
            prover_model=args.prover_model,
            output_dir=args.output_dir,
            eval_file_path=args.eval_file_path,
            pass_at_n=args.pass_at_n,
            correction_samples=1,
            correction_rounds=args.correction_rounds,
            gpu=args.gpu,
            cpu=cpu,
            nodes=args.nodes,
            negated=False,
            max_model_len=args.max_model_len,
            baseline=args.baseline,
            conjecturer_model=args.conjecturer_model,
            run_tag=args.prover_tag,
        )
    elif args.mode == "llm_baseline":
        run_llm_baseline(
            problem_path=problem_path,
            problem_name=problem_name,
            base_output_dir=args.output_dir,
            prover_model=args.prover_model,
            num_cpu=cpu,
            gpu=args.gpu,
            nodes=args.nodes,
            pass_at_n=args.pass_at_n,
            correction_rounds=args.correction_rounds,
            max_model_len=args.max_model_len,
        )
    else:
        run_ecp_multi_round(
            problem_path=problem_path,
            problem_name=problem_name,
            base_output_dir=args.output_dir,
            baseline=args.baseline,
            conjecturer_model=args.conjecturer_model,
            prover_model=args.prover_model,
            temp_formalization_dir=args.temp_formalization_dir,
            num_cpu=cpu,
            gpu=args.gpu,
            nodes=args.nodes,
            pass_at_n=args.pass_at_n,
            correction_rounds=args.correction_rounds,
            equivalence_prover_model=args.equivalence_prover_model,
            equivalence_pass_at_n=args.equivalence_pass_at_n,
            equivalence_correction_rounds=args.equivalence_correction_rounds,
            max_rounds=args.max_rounds,
            max_model_len=args.max_model_len,
            enable_enhanced_equivalence=args.enable_enhanced_equivalence,
            enable_negated_proof=args.enable_negated_proof,
            enable_final_automation=args.enable_final_automation,
            resume=args.resume,
        )


if __name__ == "__main__":
    main()
