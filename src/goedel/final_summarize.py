# src/goedel/final_summarize.py
import os
import json
import argparse
import random
import re
from typing import Any, Dict, Optional, List, Set, Tuple

import pandas as pd


DATASET_PATHS = [
    "data/dataset/test.json",
    "data/dataset/matharena.json",
    "data/dataset/constructive.json",
    "data/dataset/putnam.json",
]

CATEGORIES = (
    ("AIMEI", "AIMEI_"),
    ("AIMEII", "AIMEII_"),
    ("HMMT", "HMMT_"),
    ("APEX", "APEX_"),
    ("putnam", "putnam_"),
)


def _category_for(problem_name: str) -> Optional[str]:
    for category, marker in CATEGORIES:
        if marker in problem_name:
            return category
    return None


def _origins_by_category(origins: List[str]) -> Dict[str, List[str]]:
    grouped: Dict[str, List[str]] = {category: [] for category, _ in CATEGORIES}
    for origin in origins:
        category = _category_for(str(origin))
        if category is not None:
            grouped[category].append(str(origin))
    return {category: sorted(values) for category, values in grouped.items() if values}


def _power_of_two_pass_values(max_k: int) -> List[int]:
    values: List[int] = []
    t = 1
    while t <= max_k:
        values.append(t)
        t *= 2
    return values


def _origin_from_problem_id(problem_id: Any) -> str:
    text = str(problem_id or "")
    match = re.match(r"^(?P<origin>.+?)_g\d+(?:_corr\d+_g\d+)*$", text)
    if match:
        return match.group("origin")
    return text


# -------------------------
# Shared correctness logic
# -------------------------
def is_correct_row(compilation_result: Dict[str, Any], code: Any, field: str = "complete") -> bool:
    """
    Must match summarize.py's definition.
    """
    try:
        ok = bool(compilation_result.get(field, False))
    except Exception:
        ok = False
    if not ok:
        return False

    if code is None:
        return False
    if not isinstance(code, str):
        code = str(code)

    # Keep your existing filters:
    if "apply?" in code or "exact?" in code:
        return False
    return True


# -------------------------
# id_maps helpers
# -------------------------
def _extract_generation_id_from_id_maps(id_maps) -> Optional[str]:
    """
    id_maps is typically a list like:
      [{"origin_problem_id": ...}, {"generation_id": ...}, {"corr1_id": ...}, ...]
    Return the generation_id if present.
    """
    if not isinstance(id_maps, list):
        return None
    for d in id_maps:
        if isinstance(d, dict) and "generation_id" in d:
            return d["generation_id"]
    return None


def _build_pid_to_genid_map(full_records_path: str) -> Dict[str, str]:
    """
    Build map: (this round's) problem_id -> canonical generation_id.
    """
    if not os.path.exists(full_records_path):
        return {}

    df = pd.read_json(full_records_path)

    if "problem_id" not in df.columns or "id_maps" not in df.columns:
        return {}

    pid_to_gen: Dict[str, str] = {}
    for pid, id_maps in zip(df["problem_id"], df["id_maps"]):
        if pid is None:
            continue
        gen = _extract_generation_id_from_id_maps(id_maps)
        if gen is None:
            continue
        pid_to_gen[str(pid)] = str(gen)
    return pid_to_gen


# -------------------------
# Load compilation JSON
# -------------------------
def _load_compile_json(path: str, field: str) -> pd.DataFrame:
    """
    Expected columns in compile output:
      - name or problem_id
      - code (or full_code)
      - compilation_result (dict)
    Returns df with columns: problem_id, correct (0/1)
    """
    df = pd.read_json(path)
    if len(df) == 0:
        return pd.DataFrame({"problem_id": pd.Series(dtype=str), "correct": pd.Series(dtype=int)})

    # Normalize id column
    if "problem_id" not in df.columns and "name" in df.columns:
        df["problem_id"] = df["name"]
    elif "problem_id" in df.columns and "name" in df.columns:
        df["problem_id"] = df["problem_id"].where(df["problem_id"].notna(), df["name"])
    elif "problem_id" in df.columns and "name" not in df.columns:
        df["name"] = df["problem_id"]

    # Normalize code column
    if "code" not in df.columns and "full_code" in df.columns:
        df["code"] = df["full_code"]

    if "problem_id" not in df.columns:
        raise RuntimeError(f"{path} missing problem_id/name column")

    if "compilation_result" not in df.columns:
        # Be defensive: if missing, treat as all incorrect
        df["compilation_result"] = [{} for _ in range(len(df))]

    if "code" not in df.columns:
        df["code"] = [""] * len(df)

    df["correct"] = df.apply(
        lambda row: int(is_correct_row(row.get("compilation_result", {}), row.get("code", ""), field=field)),
        axis=1,
    )

    return df[["problem_id", "correct"]].copy()


def _load_automation_solved_origins(base_dir: str, max_round: int, field: str) -> Set[str]:
    solved: Set[str] = set()
    for r in range(0, max_round + 1):
        suffix = "" if r == 0 else f"_corr{r}"
        path = os.path.join(base_dir, f"code_compilation_repl{suffix}.json")
        if not os.path.exists(path):
            continue

        try:
            with open(path, "r", encoding="utf-8") as f:
                rows = json.load(f)
        except Exception:
            continue
        if not isinstance(rows, list):
            continue

        for row in rows:
            if not isinstance(row, dict) or not row.get("automation_fallback_preseeded"):
                continue
            comp = row.get("compilation_result") or {}
            if not isinstance(comp, dict):
                comp = {}
            code = row.get("code") if row.get("code") is not None else row.get("full_code")
            if not is_correct_row(comp, code, field=field):
                continue
            origin = _origin_from_problem_id(
                row.get("origin_problem_id") or row.get("name") or row.get("problem_id")
            )
            if origin:
                solved.add(origin)
    return solved


# -------------------------
# Formalization filter
# -------------------------
def _load_formalized_problem_map() -> Dict[str, bool]:
    """
    Load dataset JSONs and build:
      name -> (is_formalized == "True")
    Uses .get('is_formalized','False') for safety.
    """
    mp: Dict[str, bool] = {}
    for p in DATASET_PATHS:
        if not os.path.exists(p):
            continue
        try:
            with open(p, "r") as f:
                data = json.load(f)
        except Exception:
            continue

        if not isinstance(data, list):
            continue

        for row in data:
            if not isinstance(row, dict):
                continue
            name = row.get("name")
            if name is None:
                continue
            is_formalized = row.get("is_formalized", "False") == "True"
            mp[str(name)] = bool(is_formalized)

    return mp


def _is_final_proof_dir(path: str) -> bool:
    return "final_proof_" in os.path.abspath(str(path))


def _load_formalized_dataset_origin_sets() -> List[Tuple[str, Set[str]]]:
    out: List[Tuple[str, Set[str]]] = []
    for path in DATASET_PATHS:
        if not os.path.exists(path):
            continue
        try:
            with open(path, "r", encoding="utf-8") as f:
                rows = json.load(f)
        except Exception:
            continue
        if not isinstance(rows, list):
            continue
        names = {
            str(row.get("name"))
            for row in rows
            if isinstance(row, dict)
            and row.get("name") is not None
            and row.get("is_formalized", "False") == "True"
        }
        if names:
            out.append((path, names))
    return out


def _infer_expected_origins(observed_origins: List[str], base_dir: str) -> Optional[Set[str]]:
    if not _is_final_proof_dir(base_dir):
        return None
    observed = {str(origin) for origin in observed_origins if origin is not None}
    if not observed:
        return None
    candidates: List[Tuple[int, str, Set[str]]] = []
    for dataset_path, names in _load_formalized_dataset_origin_sets():
        if observed.issubset(names):
            candidates.append((len(names), dataset_path, names))
    if not candidates:
        return None
    _, _, names = sorted(candidates, key=lambda item: item[0])[0]
    return set(names)


# -------------------------
# Metrics helpers
# -------------------------
def _compute_passk_and_pass1(
    origins: List[str],
    pids_by_origin: Dict[str, List[str]],
    ever_correct: Dict[str, bool],
    sampled_gen_by_origin: Dict[str, str],
) -> Tuple[float, int, float, int]:
    """
    Returns:
      pass@k_acc, pass@k_num_solved, pass@1_acc, pass@1_num_solved
    """
    if not origins:
        return 0.0, 0, 0.0, 0

    denom = len(origins)
    passk_hits = []
    pass1_hits = []

    for o in origins:
        gens = pids_by_origin.get(o, [])
        passk_hits.append(int(any(ever_correct.get(gen, False) for gen in gens)))

        sg = sampled_gen_by_origin.get(o)
        pass1_hits.append(int(bool(ever_correct.get(sg, False))) if sg is not None else 0)

    passk_num = int(sum(passk_hits))
    pass1_num = int(sum(pass1_hits))
    passk_acc = float(passk_num / denom)
    pass1_acc = float(pass1_num / denom)
    return passk_acc, passk_num, pass1_acc, pass1_num


def _compute_sampled_pass_at_t(
    origins: List[str],
    pids_by_origin: Dict[str, List[str]],
    ever_correct: Dict[str, bool],
    t: int,
    seed: int,
) -> Tuple[float, int]:
    """
    "Sampled pass@t": for each origin, randomly sample t distinct genids (without replacement)
    and success if ANY of the sampled genids is correct under ever_correct.

    Returns: (accuracy, num_solved_instances)

    Notes:
      - If an origin has < t genids, we sample all of them (so sampled pass@t == pass@k for that origin).
      - Deterministic given (seed, t) because we use a per-(t) RNG that is advanced per-origin.
    """
    if not origins:
        return 0.0, 0

    denom = len(origins)
    rng = random.Random(f"{seed}|{t}|C0FFEE")  # stable across runs, varies with t
    hits = []

    for o in origins:
        gens = pids_by_origin.get(o, [])
        if not gens:
            hits.append(0)
            continue

        if t >= len(gens):
            chosen = gens
        else:
            # random.sample requires t <= len(gens)
            chosen = rng.sample(gens, t)

        hits.append(int(any(ever_correct.get(gen, False) for gen in chosen)))

    num = int(sum(hits))
    acc = float(num / denom)
    return acc, num


def _compute_round_metrics(
    origins: List[str],
    pids_by_origin: Dict[str, List[str]],
    ever_correct: Dict[str, bool],
    sampled_gen_by_origin: Dict[str, str],
) -> Dict[str, Any]:
    passk_acc, passk_num, pass1_acc, pass1_num = _compute_passk_and_pass1(
        origins=origins,
        pids_by_origin=pids_by_origin,
        ever_correct=ever_correct,
        sampled_gen_by_origin=sampled_gen_by_origin,
    )
    return {
        "pass@k": passk_acc,
        "pass@k_num_solved_instances": passk_num,
        "pass@1": pass1_acc,
        "pass@1_num_solved_instances": pass1_num,
    }


def _build_sampled_pass_curve(
    origins: List[str],
    pids_by_origin: Dict[str, List[str]],
    ever_correct: Dict[str, bool],
    seed: int,
    pass_values: Optional[List[int]] = None,
) -> Tuple[int, Dict[str, Dict[str, Any]]]:
    max_k = max((len(pids_by_origin[o]) for o in origins), default=0)
    sampled_pass_curve: Dict[str, Dict[str, Any]] = {}
    values = pass_values if pass_values is not None else _power_of_two_pass_values(max_k)
    for t in values:
        acc_t, num_t = _compute_sampled_pass_at_t(
            origins=origins,
            pids_by_origin=pids_by_origin,
            ever_correct=ever_correct,
            t=t,
            seed=seed,
        )
        sampled_pass_curve[f"{t}"] = {
            "accuracy": acc_t,
            "num_solved_instances": num_t,
        }
    return max_k, sampled_pass_curve


def _aggregate_sampled_pass_curves(
    pass_values: List[int],
    denom: int,
    group_curves: List[Dict[str, Dict[str, Any]]],
) -> Dict[str, Dict[str, Any]]:
    sampled_pass_curve: Dict[str, Dict[str, Any]] = {}
    for t in pass_values:
        key = str(t)
        num_t = int(
            sum(
                int(curve.get(key, {}).get("num_solved_instances", 0))
                for curve in group_curves
            )
        )
        sampled_pass_curve[key] = {
            "accuracy": float(num_t / denom) if denom else 0.0,
            "num_solved_instances": num_t,
        }
    return sampled_pass_curve


# -------------------------
# CLI
# -------------------------
def build_arg_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--base_output_dir",
        type=str,
        required=True,
        help="Base output directory where code_compilation_repl*.json and full_records*.json live.",
    )
    parser.add_argument(
        "--max_round",
        type=int,
        required=True,
        help="Maximum correction round index (inclusive).",
    )
    parser.add_argument(
        "--output_dir",
        type=str,
        required=True,
        help="Directory to write final_metrics.json into.",
    )
    parser.add_argument(
        "--field",
        default="complete",
        choices=["complete", "pass"],
        type=str,
        help="Which compilation_result field to use.",
    )
    parser.add_argument(
        "--seed",
        default=0,
        type=int,
        help="RNG seed for simulated pass@1 and sampled pass@t curves.",
    )
    return parser


def main():
    args = build_arg_parser().parse_args()

    base_dir = args.base_output_dir
    max_round = args.max_round
    out_dir = args.output_dir
    os.makedirs(out_dir, exist_ok=True)

    # -------- Load formalization map (name -> bool) --------
    formalized_problems = _load_formalized_problem_map()

    # -------- Load round0 full_records to get origin + generation mapping --------
    full0_path = os.path.join(base_dir, "full_records.json")
    if not os.path.exists(full0_path):
        raise FileNotFoundError(f"Missing {full0_path} (needed to map problem_id -> origin_problem_id/generation_id).")

    df_full0 = pd.read_json(full0_path)
    if "problem_id" not in df_full0.columns:
        raise RuntimeError("full_records.json missing 'problem_id'")
    if "origin_problem_id" not in df_full0.columns:
        raise RuntimeError("full_records.json missing 'origin_problem_id' (expected from inference).")

    # Build mapping pid->genid for round0 (robust)
    pid_to_gen_round0 = _build_pid_to_genid_map(full0_path)

    # Build origin -> list of canonical generation_ids (NOT correction ids)
    pids_by_origin: Dict[str, List[str]] = {}
    for pid, origin in zip(df_full0["problem_id"], df_full0["origin_problem_id"]):
        if pid is None or origin is None:
            continue
        pid = str(pid)
        origin = str(origin)
        gen = pid_to_gen_round0.get(pid, pid)  # round0 often already equals generation_id
        pids_by_origin.setdefault(origin, []).append(gen)

    all_origins = sorted(pids_by_origin.keys())
    if not all_origins:
        raise RuntimeError("No origins found in full_records.json; cannot compute metrics.")

    expected_origins = _infer_expected_origins(all_origins, base_dir)
    if expected_origins:
        for origin in expected_origins:
            pids_by_origin.setdefault(origin, [])
        all_origins = sorted(expected_origins)

    # Filter benchmark origins globally: ONLY count origins with is_formalized == True.
    # Ad-hoc demo/custom JSONL inputs are not present in the benchmark dataset
    # files, so score all observed origins when none of them are known there.
    known_origins = [o for o in all_origins if o in formalized_problems]
    if known_origins:
        origins = [o for o in all_origins if formalized_problems.get(o, False)]
    else:
        origins = list(all_origins)
    if not origins:
        raise RuntimeError(
            "After filtering by is_formalized==True, there are 0 origins to score. "
            "Check dataset JSONs and origin_problem_id naming."
        )
    num_origins = len(origins)

    # -------- Load round0 compilation --------
    comp0_path = os.path.join(base_dir, "code_compilation_repl.json")
    if not os.path.exists(comp0_path):
        raise FileNotFoundError(f"Missing {comp0_path}")

    df0 = _load_compile_json(comp0_path, field=args.field)

    # Map round0 compile id -> canonical genid, then to correctness
    correct0_by_genid: Dict[str, int] = {}
    for pid, corr in zip(df0["problem_id"], df0["correct"]):
        pid = str(pid)
        gen = pid_to_gen_round0.get(pid, pid)
        prev = correct0_by_genid.get(gen, 0)
        correct0_by_genid[gen] = max(prev, int(corr))

    # -------- Initialize cumulative correctness (ever_correct up to current round) --------
    ever_correct: Dict[str, bool] = {gen: bool(v) for gen, v in correct0_by_genid.items()}
    # Ensure all genids appearing in round0 full_records are present
    for o in all_origins:
        for gen in pids_by_origin[o]:
            ever_correct.setdefault(gen, False)

    # -------- Fix the simulated pass@1 sample per origin (same sample across rounds) --------
    rng = random.Random(args.seed)
    sampled_gen_by_origin: Dict[str, str] = {}
    for o in origins:
        if pids_by_origin[o]:
            sampled_gen_by_origin[o] = rng.choice(pids_by_origin[o])

    origins_by_category = _origins_by_category(origins)
    automation_solved_origin_set = _load_automation_solved_origins(
        base_dir=base_dir,
        max_round=max_round,
        field=args.field,
    ) & set(origins)

    # -------- Compute metrics at each round: 0..max_round --------
    per_round: Dict[str, Dict[str, Any]] = {}
    category_per_round: Dict[str, Dict[str, Dict[str, Any]]] = {
        category: {} for category in origins_by_category
    }

    # Round 0 metrics (cumulative == round0)
    per_round["round_0"] = _compute_round_metrics(
        origins=origins,
        pids_by_origin=pids_by_origin,
        ever_correct=ever_correct,
        sampled_gen_by_origin=sampled_gen_by_origin,
    )
    for category, category_origins in origins_by_category.items():
        category_per_round[category]["round_0"] = _compute_round_metrics(
            origins=category_origins,
            pids_by_origin=pids_by_origin,
            ever_correct=ever_correct,
            sampled_gen_by_origin=sampled_gen_by_origin,
        )

    # Incorporate correction rounds, and compute cumulative metrics at each round r
    for r in range(1, max_round + 1):
        comp_r = os.path.join(base_dir, f"code_compilation_repl_corr{r}.json")
        full_r = os.path.join(base_dir, f"full_records_corr{r}.json")

        if os.path.exists(comp_r):
            pid_to_gen_r = _build_pid_to_genid_map(full_r)
            dfr = _load_compile_json(comp_r, field=args.field)

            updated = 0
            for pid, corr in zip(dfr["problem_id"], dfr["correct"]):
                pid = str(pid)
                gen = pid_to_gen_r.get(pid)

                # Fallbacks if mapping missing:
                # - try round0 pid->gen
                # - else assume pid already equals genid
                if gen is None:
                    gen = pid_to_gen_round0.get(pid, pid)

                if bool(corr):
                    if not ever_correct.get(gen, False):
                        updated += 1
                    ever_correct[gen] = True

            print(f"[final_summarize] round {r}: loaded {comp_r}, newly-solved(genid)={updated}")
        else:
            print(f"[final_summarize] round {r}: missing {comp_r}; keeping cumulative metrics unchanged")

        per_round[f"round_{r}"] = _compute_round_metrics(
            origins=origins,
            pids_by_origin=pids_by_origin,
            ever_correct=ever_correct,
            sampled_gen_by_origin=sampled_gen_by_origin,
        )
        for category, category_origins in origins_by_category.items():
            category_per_round[category][f"round_{r}"] = _compute_round_metrics(
                origins=category_origins,
                pids_by_origin=pids_by_origin,
                ever_correct=ever_correct,
                sampled_gen_by_origin=sampled_gen_by_origin,
            )

    # -------- At final round: record sampled pass@t for powers of two up to k --------
    # Define k as the maximum number of genids across the scored origins.
    # (So pass@t is meaningful up to that max; for origins with <t genids we sample all.)
    max_k = max((len(pids_by_origin[o]) for o in origins), default=0)
    final_pass_values = _power_of_two_pass_values(max_k)

    category_metrics: Dict[str, Dict[str, Any]] = {}
    sampled_curve_groups: List[Dict[str, Dict[str, Any]]] = []
    categorized_origins: Set[str] = set()
    for category, category_origins in origins_by_category.items():
        category_max_k, category_sampled_pass_curve = _build_sampled_pass_curve(
            origins=category_origins,
            pids_by_origin=pids_by_origin,
            ever_correct=ever_correct,
            seed=args.seed,
            pass_values=final_pass_values,
        )
        sampled_curve_groups.append(category_sampled_pass_curve)
        categorized_origins.update(category_origins)
        category_last = category_per_round[category][f"round_{max_round}"]
        category_metrics[category] = {
            "num_origins": int(len(category_origins)),
            "automation_solved_num_instances": int(
                sum(1 for origin in category_origins if origin in automation_solved_origin_set)
            ),
            "pass@1_with_correction": float(category_last["pass@1"]),
            "pass@1_with_correction_num_solved_instances": int(category_last["pass@1_num_solved_instances"]),
            "pass@k_with_correction": float(category_last["pass@k"]),
            "pass@k_with_correction_num_solved_instances": int(category_last["pass@k_num_solved_instances"]),
            "per_round": category_per_round[category],
            "final_round_sampled_pass_curve": {
                "max_k_over_origins": int(category_max_k),
                "pass_curve": category_sampled_pass_curve,
            },
        }

    uncategorized_origins = [origin for origin in origins if origin not in categorized_origins]
    if uncategorized_origins:
        _, uncategorized_sampled_pass_curve = _build_sampled_pass_curve(
            origins=uncategorized_origins,
            pids_by_origin=pids_by_origin,
            ever_correct=ever_correct,
            seed=args.seed,
            pass_values=final_pass_values,
        )
        sampled_curve_groups.append(uncategorized_sampled_pass_curve)

    if sampled_curve_groups:
        sampled_pass_curve = _aggregate_sampled_pass_curves(
            pass_values=final_pass_values,
            denom=num_origins,
            group_curves=sampled_curve_groups,
        )
    else:
        _, sampled_pass_curve = _build_sampled_pass_curve(
            origins=origins,
            pids_by_origin=pids_by_origin,
            ever_correct=ever_correct,
            seed=args.seed,
            pass_values=final_pass_values,
        )

    # -------- Final summary (ONLY for formalized origins) --------
    final_summary = []
    for origin in origins:
        solved = any(bool(ever_correct.get(gen, False)) for gen in pids_by_origin[origin])
        final_summary.append(
            {
                "name": str(origin),
                "is_solved": "True" if solved else "False",
            }
        )

    final_summary_path = os.path.join(out_dir, "final_summary.json")
    with open(final_summary_path, "w") as f:
        json.dump(final_summary, f, indent=2, ensure_ascii=False)
    print(f"[final_summarize] Wrote: {final_summary_path}")

    # -------- Final metrics JSON --------
    last_key = f"round_{max_round}"
    out = {
        "seed": int(args.seed),
        "field": args.field,
        "max_round": int(max_round),
        "num_origins": int(num_origins),
        "automation_solved_num_instances": int(len(automation_solved_origin_set)),

        # Convenience aliases (final / max_round cumulative)
        "pass@1_with_correction": float(per_round[last_key]["pass@1"]),
        "pass@1_with_correction_num_solved_instances": int(per_round[last_key]["pass@1_num_solved_instances"]),
        "pass@k_with_correction": float(per_round[last_key]["pass@k"]),
        "pass@k_with_correction_num_solved_instances": int(per_round[last_key]["pass@k_num_solved_instances"]),

        # Per-round full traces
        "per_round": per_round,

        # New: sampled pass@t curve at final round, for powers of two up to max_k
        "final_round_sampled_pass_curve": {
            "max_k_over_origins": int(max_k),
            "pass_curve": sampled_pass_curve,
        },
        "category_metrics": category_metrics,
    }

    out_path = os.path.join(out_dir, "final_metrics.json")
    with open(out_path, "w") as f:
        json.dump(out, f, indent=2)
    print(f"[final_summarize] Wrote: {out_path}")

    # Pretty prints: round0 and final
    r0 = per_round["round_0"]
    rf = per_round[last_key]
    print(f"[final_summarize] (scored num_origins={num_origins})")
    print(f"[final_summarize] round 0  pass@k = {r0['pass@k']:.6f}  ({r0['pass@k_num_solved_instances']}/{num_origins})")
    print(f"[final_summarize] round 0  pass@1 = {r0['pass@1']:.6f}  ({r0['pass@1_num_solved_instances']}/{num_origins})")
    print(f"[final_summarize] round {max_round} pass@k = {rf['pass@k']:.6f}  ({rf['pass@k_num_solved_instances']}/{num_origins})")
    print(f"[final_summarize] round {max_round} pass@1 = {rf['pass@1']:.6f}  ({rf['pass@1_num_solved_instances']}/{num_origins})")
    if max_k > 0:
        displayed_t_values = _power_of_two_pass_values(max_k)
        last_displayed_t = displayed_t_values[-1] if displayed_t_values else max_k
        p1 = sampled_pass_curve.get("1", {}).get("accuracy", None)
        pk = sampled_pass_curve.get(str(last_displayed_t), {}).get("accuracy", None)
        if p1 is not None and pk is not None:
            print(f"[final_summarize] final round sampled curve: pass@1={p1:.6f}, pass@{last_displayed_t}={pk:.6f}")
    if category_metrics:
        category_bits = []
        for category, metrics in category_metrics.items():
            solved = metrics["pass@k_with_correction_num_solved_instances"]
            total = metrics["num_origins"]
            acc = metrics["pass@k_with_correction"]
            category_bits.append(f"{category}: pass@k={acc:.6f} ({solved}/{total})")
        print("[final_summarize] categories: " + "; ".join(category_bits))


if __name__ == "__main__":
    main()
