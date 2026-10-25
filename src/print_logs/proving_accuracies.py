import argparse
import csv
import json
import random
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


PROJECT_ROOT = Path(__file__).resolve().parents[2]
OUTPUT_ROOT = PROJECT_ROOT / "output_artifact_eval"
REPORT_PATH = PROJECT_ROOT / "src/print_logs/accuracies/proving_accuracies.txt"

DATASETS = ("matharena", "putnam")
BASELINES = ("cot", "mcp")
PROVER_MODELS = ("Goedel-Prover-V2-8B", "Goedel-Prover-V2-32B")
LLM_BASELINE_MODELS = ("gpt-5", "Goedel-Prover-V2-32B")
ROUNDS = (0, 2)
PASS_AT_VALUES = (4, 32)
SKIP_PASS_AT_BY_LABEL = {
    "putnam_llm_baseline_gpt-5": {32},
}

CATEGORIES = (
    ("AIMEI", "AIMEI_"),
    ("AIMEII", "AIMEII_"),
    ("HMMT", "HMMT_"),
    ("APEX", "APEX_"),
    ("putnam", "putnam_"),
)


@dataclass(frozen=True)
class ExperimentSpec:
    label: str
    folder: Path
    is_ecp: bool
    dataset: str
    prover_or_model: str
    baseline: str | None = None


@dataclass(frozen=True)
class Metric:
    accuracy: float
    solved: int
    total: int


def load_json(path: Path) -> Any:
    with path.open(encoding="utf-8") as f:
        return json.load(f)


def category_for(problem_name: str) -> str | None:
    for category, marker in CATEGORIES:
        if marker in problem_name:
            return category
    return None


def metric_text(metric: Metric | None) -> str:
    if metric is None:
        return "N/A"
    return f"{metric.accuracy:.4f} ({metric.solved}/{metric.total})"


def origin_from_generation_id(generation_id: str) -> str:
    match = re.match(r"^(?P<origin>.+?)_g\d+$", generation_id)
    if match:
        return match.group("origin")
    return generation_id


def origins_by_category(origins: list[str]) -> dict[str, list[str]]:
    grouped: dict[str, list[str]] = {category: [] for category, _ in CATEGORIES}
    for origin in origins:
        category = category_for(origin)
        if category is not None:
            grouped[category].append(origin)
    return {category: sorted(values) for category, values in grouped.items() if values}


def compute_sampled_pass_at(
    origins: list[str],
    pids_by_origin: dict[str, list[str]],
    ever_correct: dict[str, bool],
    pass_at: int,
    seed: int,
) -> Metric:
    rng = random.Random(f"{seed}|{pass_at}|C0FFEE")
    hits = 0
    for origin in origins:
        generation_ids = pids_by_origin.get(origin, [])
        if not generation_ids:
            continue
        if pass_at >= len(generation_ids):
            chosen = generation_ids
        else:
            chosen = rng.sample(generation_ids, pass_at)
        hits += int(any(ever_correct.get(generation_id, False) for generation_id in chosen))

    total = len(origins)
    accuracy = float(hits / total) if total else 0.0
    return Metric(accuracy=accuracy, solved=hits, total=total)


def read_summary_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f, delimiter="\t", quotechar='"'))


def load_origins_from_round_summary(base_dir: Path) -> list[str]:
    path = base_dir / "summary_round_0/origin_problem_id_summarize.csv"
    if not path.exists():
        raise FileNotFoundError(path)
    rows = read_summary_tsv(path)
    origins = [
        str(row["origin_problem_id"])
        for row in rows
        if row.get("origin_problem_id") not in (None, "")
    ]
    if not origins:
        raise RuntimeError(f"No origins found in {path}")
    return sorted(origins)


def load_generation_correctness_from_round_summary(
    base_dir: Path,
    round_index: int,
) -> dict[str, bool]:
    path = base_dir / f"summary_round_{round_index}/generation_id_summarize.csv"
    if not path.exists():
        if round_index == 0:
            raise FileNotFoundError(path)
        return {}

    correctness: dict[str, bool] = {}
    for row in read_summary_tsv(path):
        generation_id = row.get("generation_id")
        if not generation_id:
            continue
        try:
            solved_count = int(float(row.get("sum", "0")))
        except ValueError:
            solved_count = 0
        correctness[str(generation_id)] = solved_count > 0
    return correctness


def compute_metrics_from_round_summaries(
    base_dir: Path,
    final_metrics: dict[str, Any],
) -> dict[str, dict[int, dict[int, Metric]]]:
    seed = int(final_metrics.get("seed", 0))
    max_round = int(final_metrics.get("max_round", max(ROUNDS)))

    origins = load_origins_from_round_summary(base_dir)
    category_origins = origins_by_category(origins)
    pids_by_origin: dict[str, list[str]] = {origin: [] for origin in origins}

    round0_correctness = load_generation_correctness_from_round_summary(base_dir, 0)
    for generation_id in round0_correctness:
        origin = origin_from_generation_id(generation_id)
        pids_by_origin.setdefault(origin, []).append(generation_id)
    for generation_ids in pids_by_origin.values():
        generation_ids.sort()

    ever_correct = {generation_id: bool(correct) for generation_id, correct in round0_correctness.items()}
    metrics_by_scope: dict[str, dict[int, dict[int, Metric]]] = {}

    def capture(round_index: int) -> None:
        if round_index not in ROUNDS:
            return
        scopes = {"overall": origins, **category_origins}
        for scope, scope_origins in scopes.items():
            metrics_by_scope.setdefault(scope, {}).setdefault(round_index, {})
            for pass_at in PASS_AT_VALUES:
                metrics_by_scope[scope][round_index][pass_at] = compute_sampled_pass_at(
                    origins=scope_origins,
                    pids_by_origin=pids_by_origin,
                    ever_correct=ever_correct,
                    pass_at=pass_at,
                    seed=seed,
                )

    capture(0)
    for round_index in range(1, max_round + 1):
        for generation_id, correct in load_generation_correctness_from_round_summary(
            base_dir, round_index
        ).items():
            ever_correct.setdefault(generation_id, False)
            if correct:
                ever_correct[generation_id] = True
        capture(round_index)

    return metrics_by_scope


def metric_from_mapping(mapping: dict[str, Any], pass_at: int, total: int) -> Metric | None:
    entry = mapping.get(str(pass_at))
    if not isinstance(entry, dict):
        return None
    accuracy = entry.get("accuracy")
    solved = entry.get("num_solved_instances")
    if accuracy is None or solved is None:
        return None
    return Metric(accuracy=float(accuracy), solved=int(solved), total=total)


def fallback_metric_from_final_metrics(
    scope_metrics: dict[str, Any],
    round_index: int,
    pass_at: int,
) -> Metric | None:
    total = int(scope_metrics.get("num_origins", 0))
    max_round = int(scope_metrics.get("max_round", 2))
    if "num_origins" not in scope_metrics and "per_round" in scope_metrics:
        # Category entries do have num_origins; overall final_metrics also has it.
        total = int(scope_metrics.get("num_origins", 0))

    if round_index == max_round:
        curve = (
            scope_metrics.get("final_round_sampled_pass_curve", {})
            .get("pass_curve", {})
        )
        if isinstance(curve, dict):
            metric = metric_from_mapping(curve, pass_at, total)
            if metric is not None:
                return metric

    max_k = (
        scope_metrics.get("final_round_sampled_pass_curve", {})
        .get("max_k_over_origins")
    )
    round_metrics = scope_metrics.get("per_round", {}).get(f"round_{round_index}", {})
    if max_k is not None and pass_at >= int(max_k) and isinstance(round_metrics, dict):
        solved = round_metrics.get("pass@k_num_solved_instances")
        accuracy = round_metrics.get("pass@k")
        if solved is not None and accuracy is not None:
            return Metric(accuracy=float(accuracy), solved=int(solved), total=total)
    return None


def fallback_metrics_from_final_json(
    final_metrics: dict[str, Any],
    pass_at_values: tuple[int, ...] = PASS_AT_VALUES,
) -> dict[str, dict[int, dict[int, Metric]]]:
    metrics_by_scope: dict[str, dict[int, dict[int, Metric]]] = {}
    scopes: dict[str, dict[str, Any]] = {"overall": final_metrics}
    category_metrics = final_metrics.get("category_metrics", {})
    if isinstance(category_metrics, dict):
        for category, metrics in category_metrics.items():
            if isinstance(metrics, dict):
                scoped = dict(metrics)
                scoped.setdefault("max_round", final_metrics.get("max_round", 2))
                scopes[str(category)] = scoped

    for scope, scope_metrics in scopes.items():
        for round_index in ROUNDS:
            for pass_at in pass_at_values:
                metric = fallback_metric_from_final_metrics(scope_metrics, round_index, pass_at)
                if metric is None:
                    continue
                metrics_by_scope.setdefault(scope, {}).setdefault(round_index, {})[pass_at] = metric
    return metrics_by_scope


def pass_at_values_for_spec(spec: ExperimentSpec) -> tuple[int, ...]:
    skipped = SKIP_PASS_AT_BY_LABEL.get(spec.label, set())
    return tuple(pass_at for pass_at in PASS_AT_VALUES if pass_at not in skipped)


def experiment_specs(output_root: Path) -> list[ExperimentSpec]:
    specs: list[ExperimentSpec] = []
    for dataset in DATASETS:
        for baseline in BASELINES:
            for prover_model in PROVER_MODELS:
                folder = output_root / f"{dataset}_gpt-5_{baseline}_{prover_model}"
                specs.append(
                    ExperimentSpec(
                        label=folder.name,
                        folder=folder,
                        is_ecp=True,
                        dataset=dataset,
                        baseline=baseline,
                        prover_or_model=prover_model,
                    )
                )

    for dataset in DATASETS:
        for model in LLM_BASELINE_MODELS:
            folder = output_root / f"{dataset}_llm_baseline_{model}"
            specs.append(
                ExperimentSpec(
                    label=folder.name,
                    folder=folder,
                    is_ecp=False,
                    dataset=dataset,
                    prover_or_model=model,
                )
            )
    return specs


def find_final_metrics_path(spec: ExperimentSpec) -> Path | None:
    if spec.is_ecp:
        expected = (
            spec.folder
            / "final_proof_1"
            / "prover"
            / f"{spec.dataset}_gpt-5_{spec.baseline}_final_1"
            / spec.prover_or_model
            / "final_summary/final_metrics.json"
        )
        if expected.exists():
            return expected

        matches = sorted(
            (spec.folder / "final_proof_1").glob("**/final_summary/final_metrics.json")
        )
        return matches[0] if matches else None

    expected = (
        spec.folder
        / "prover"
        / "llm_baseline"
        / spec.prover_or_model
        / "final_summary/final_metrics.json"
    )
    if expected.exists():
        return expected

    matches = sorted(
        (spec.folder / "prover" / "llm_baseline").glob(
            "**/final_summary/final_metrics.json"
        )
    )
    return matches[0] if matches else None


def merge_metric_maps(
    primary: dict[str, dict[int, dict[int, Metric]]],
    fallback: dict[str, dict[int, dict[int, Metric]]],
) -> dict[str, dict[int, dict[int, Metric]]]:
    merged = {
        scope: {
            round_index: dict(pass_metrics)
            for round_index, pass_metrics in round_metrics.items()
        }
        for scope, round_metrics in primary.items()
    }
    for scope, round_metrics in fallback.items():
        for round_index, pass_metrics in round_metrics.items():
            for pass_at, metric in pass_metrics.items():
                merged.setdefault(scope, {}).setdefault(round_index, {}).setdefault(
                    pass_at, metric
                )
    return merged


def scope_order(metrics_by_scope: dict[str, Any]) -> list[str]:
    ordered = ["overall"]
    ordered.extend(category for category, _ in CATEGORIES if category in metrics_by_scope)
    ordered.extend(
        sorted(scope for scope in metrics_by_scope if scope not in set(ordered))
    )
    return ordered


def automation_value(
    final_metrics: dict[str, Any],
    scope: str,
    include_automation: bool,
) -> str:
    if not include_automation:
        return ""
    if scope == "overall":
        value = final_metrics.get("automation_solved_num_instances")
    else:
        value = (
            final_metrics.get("category_metrics", {})
            .get(scope, {})
            .get("automation_solved_num_instances")
        )
    return "N/A" if value is None else str(value)


def table_row(values: list[str], widths: list[int]) -> str:
    return "  " + "  ".join(value.ljust(width) for value, width in zip(values, widths)).rstrip()


def render_experiment(spec: ExperimentSpec, metrics_path: Path) -> list[str]:
    final_metrics = load_json(metrics_path)
    if not isinstance(final_metrics, dict):
        raise TypeError(f"{metrics_path} must contain a JSON object")

    pass_at_values = pass_at_values_for_spec(spec)
    metrics_by_scope = fallback_metrics_from_final_json(final_metrics, pass_at_values)
    source_note = "source: final_metrics.json only"

    include_automation = spec.is_ecp
    headers = ["scope", "round", *(f"pass@{pass_at}" for pass_at in pass_at_values)]
    if include_automation:
        headers.append("automation_solved")
    widths = [12, 7] + [18] * len(pass_at_values) + ([17] if include_automation else [])

    lines = [
        spec.label,
        f"  metrics: {metrics_path.relative_to(PROJECT_ROOT)}",
        f"  {source_note}",
        table_row(headers, widths),
        table_row(["-" * width for width in widths], widths),
    ]

    for scope in scope_order(metrics_by_scope):
        for round_index in ROUNDS:
            pass_metrics = metrics_by_scope.get(scope, {}).get(round_index, {})
            row = [
                scope,
                f"round_{round_index}",
                *(metric_text(pass_metrics.get(pass_at)) for pass_at in pass_at_values),
            ]
            if include_automation:
                row.append(automation_value(final_metrics, scope, include_automation))
            lines.append(table_row(row, widths))
    lines.append("")
    return lines


def build_report(output_root: Path) -> str:
    lines: list[str] = []
    missing: list[str] = []

    for spec in experiment_specs(output_root):
        metrics_path = find_final_metrics_path(spec)
        if metrics_path is None:
            missing.append(spec.label)
            continue
        lines.extend(render_experiment(spec, metrics_path))

    if missing:
        lines.append("Missing final_metrics.json")
        for label in missing:
            lines.append(f"  {label}")
        lines.append("")

    if not lines:
        lines.append("No target experiment metrics found.")
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Print round 0 / round 2 selected pass@k proving accuracies "
            "for the expected ECP and LLM-baseline output folders."
        )
    )
    parser.add_argument(
        "--output-root",
        type=Path,
        default=OUTPUT_ROOT,
        help="Root directory containing experiment output folders.",
    )
    parser.add_argument(
        "--report-path",
        type=Path,
        default=REPORT_PATH,
        help="Where to save a copy of the printed report.",
    )
    parser.add_argument(
        "--no-save",
        action="store_true",
        help="Only print to stdout; do not write --report-path.",
    )
    return parser


def main() -> None:
    args = build_arg_parser().parse_args()
    report = build_report(args.output_root)
    print(report, end="")

    if not args.no_save:
        args.report_path.parent.mkdir(parents=True, exist_ok=True)
        args.report_path.write_text(report, encoding="utf-8")
        print(f"Saved report to {args.report_path}")


if __name__ == "__main__":
    main()
