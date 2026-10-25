import pandas as pd
import numpy as np
import argparse
import re
import os
# at top
import json
import random
from src.goedel.metrics_utils import is_correct_row


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


def _category_for(problem_name: str):
    for category, marker in CATEGORIES:
        if marker in problem_name:
            return category
    return None


def _is_final_proof_path(*paths) -> bool:
    return any("final_proof_" in os.path.abspath(str(path)) for path in paths if path)


def _load_formalized_dataset_origin_sets():
    out = []
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


def _infer_expected_origins(observed_origins, *paths):
    if not _is_final_proof_path(*paths):
        return None
    observed = {str(origin) for origin in observed_origins if origin is not None}
    if not observed:
        return None
    candidates = []
    for dataset_path, names in _load_formalized_dataset_origin_sets():
        if observed.issubset(names):
            candidates.append((len(names), dataset_path, names))
    if not candidates:
        return None
    _, _, names = sorted(candidates, key=lambda item: item[0])[0]
    return set(names)


# replace your df["correct"] line with:

parser = argparse.ArgumentParser()
#/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/new_pipe_minif2f/code_compilation.json 
parser.add_argument('--input_path',  type=str)
#/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/new_pipe_minif2f/compilation_summarize.json
parser.add_argument('--full_record_path',  type=str)
parser.add_argument('--output_dir',  type=str)
# parser.add_argument('--group',  type=bool, default=False)

# parser.add_argument('--round',  type=int, default=0)
parser.add_argument('--field', default="complete",choices=["complete", "pass"], type=str)
args = parser.parse_args()


input_file= args.input_path
df = pd.read_json(input_file)
df_full = pd.read_json(args.full_record_path)
expected_origin_problem_ids = _infer_expected_origins(
    df_full["origin_problem_id"].dropna().astype(str).unique()
    if "origin_problem_id" in df_full.columns
    else [],
    args.input_path,
    args.full_record_path,
    args.output_dir,
)
if len(df) == 0:
    os.makedirs(args.output_dir, exist_ok=True)
    with open(f"{args.output_dir}/meta_summarize.json", "w") as f:
        json.dump([], f, indent=4)
    print(f"[summarize] Empty compilation input: {input_file}. Wrote empty meta_summarize.json and exit.")
    raise SystemExit(0)

ids_lookup = dict(zip(df_full.problem_id, df_full.id_maps))

import numpy as np

ids_num_ = np.unique(df_full.id_maps.apply(lambda x: len(x)))
assert len(ids_num_) == 1
ids_num = ids_num_[0]
first_element = df_full.id_maps[0]
# import pdb; pdb.set_trace()
# df["correct"] = df.apply(lambda row: int(  ((row["compilation_result"][args.field])) ), axis=1) #  and ("apply?" not in row["code"]) and
df["correct"] = df.apply(
    lambda row: int(is_correct_row(row["compilation_result"], row["code"], field=args.field)),
    axis=1
)
import os
os.makedirs(args.output_dir, exist_ok=True)

meta_result = []
name_list = []
for i in range(ids_num):
  names = [k for k, _ in first_element[i].items()]
  assert len(names) == 1
  name = names[0]
  name_list.append(name)
  df[name] =  df["name"].apply(lambda x: ids_lookup[x][i][name])
  df_grp = df[[name, "correct"]].groupby(name)["correct"].aggregate(["sum", "count"]).reset_index()
  if name == "origin_problem_id" and expected_origin_problem_ids:
    expected_df = pd.DataFrame({name: sorted(expected_origin_problem_ids)})
    df_grp = expected_df.merge(df_grp, on=name, how="left")
    df_grp["sum"] = df_grp["sum"].fillna(0).astype(int)
    df_grp["count"] = df_grp["count"].fillna(0).astype(int)
  df_grp.to_csv(F"{args.output_dir}/{name}_summarize.csv", index=False, header=True, sep='\t', quoting=1, na_rep='Missing')
  solved_num = int((df_grp["sum"] > 0).sum())
  problem_num = int(len(df_grp))
  solved_ratio = (solved_num / problem_num * 100) if problem_num else 0.0
  meta_result.append({
    "level": F"{name}", 
    "value": {
        "problem_num": problem_num,
        "solved_num": solved_num,
        "solved_ratio": F"{solved_ratio: 2f}"
      }
  })
  
pd.DataFrame(meta_result).to_json(F"{args.output_dir}/meta_summarize.json", indent=4, orient="records")



# ADD THIS near the end (after meta_summarize.json is written is fine)
def _write_round_metrics_round0(df, output_dir: str, seed: int = 0, expected_origins=None):
    """
    Computes:
      - pass@k without correction: any correct among k samples in round0
      - simulated pass@1 without correction: sample one problem_id per origin_problem_id
    """
    rng = random.Random(seed)

    # We assume summarize.py already added these columns:
    #   df["origin_problem_id"] exists because you create it in the loop
    # But to be safe, reconstruct it if needed:
    if "origin_problem_id" not in df.columns:
        # If you always have id_maps in df_full, you can add origin_problem_id similarly
        raise RuntimeError("origin_problem_id column missing; run summarize with level origin_problem_id first.")

    origins = (
        sorted(str(origin) for origin in expected_origins)
        if expected_origins
        else sorted(str(origin) for origin in df["origin_problem_id"].dropna().unique())
    )
    grouped = {str(origin): sub for origin, sub in df.groupby("origin_problem_id")}

    # pass@k (no correction): per origin, any correct among all its samples.
    # Origins with no generated samples count as unsolved.
    passk_hits = []
    sampled_success = []
    per_origin = {}
    for origin in origins:
        sub = grouped.get(origin)
        if sub is None or len(sub) == 0:
            passk_hit = 0
            sampled_hit = 0
            passk_hits.append(passk_hit)
            sampled_success.append(sampled_hit)
            per_origin[origin] = {
                "pass@k_no_correction": passk_hit,
                "pass@1_no_correction": sampled_hit,
            }
            continue
        passk_hit = int(sub["correct"].sum() > 0)
        rows = sub.index.tolist()
        pick = rng.choice(rows)
        sampled_hit = int(df.loc[pick, "correct"] == 1)
        passk_hits.append(passk_hit)
        sampled_success.append(sampled_hit)
        per_origin[origin] = {
            "pass@k_no_correction": passk_hit,
            "pass@1_no_correction": sampled_hit,
        }

    passk = float(sum(passk_hits) / len(origins)) if origins else 0.0
    pass1_sim = float(sum(sampled_success) / len(origins)) if origins else 0.0
    category_metrics = {}
    for category, _ in CATEGORIES:
        category_origins = [origin for origin in origins if _category_for(str(origin)) == category]
        if not category_origins:
            continue
        category_passk_num = int(sum(per_origin[origin]["pass@k_no_correction"] for origin in category_origins))
        category_pass1_num = int(sum(per_origin[origin]["pass@1_no_correction"] for origin in category_origins))
        category_total = int(len(category_origins))
        category_metrics[category] = {
            "num_origins": category_total,
            "pass@k_no_correction": float(category_passk_num / category_total),
            "pass@k_no_correction_num_solved_instances": category_passk_num,
            "pass@1_no_correction": float(category_pass1_num / category_total),
            "pass@1_no_correction_num_solved_instances": category_pass1_num,
        }

    out = {
        "round": 0,
        "seed": seed,
        "field": args.field,
        "pass@k_no_correction": passk,
        "pass@1_no_correction": pass1_sim,
        "num_origins": int(len(origins)),
        "num_rows": int(len(df)),
        "category_metrics": category_metrics,
    }
    with open(f"{output_dir}/round0_metrics.json", "w") as f:
        json.dump(out, f, indent=2)

# call it only if this summarize is running for round0:
# easiest heuristic: input file path ends with code_compilation_repl.json (no _corr suffix)
if input_file.endswith("code_compilation_repl.json"):
    _write_round_metrics_round0(df, args.output_dir, seed=0, expected_origins=expected_origin_problem_ids)
