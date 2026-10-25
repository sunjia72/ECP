import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any


PROJECT_ROOT = Path(__file__).resolve().parents[2]
OUTPUT_ROOT = PROJECT_ROOT / "output_artifact_eval"
REPORT_PATH = (
    PROJECT_ROOT / "src/print_logs/accuracies/answer_construction_accuracies.txt"
)
FOLDER_SUBSTRING = "Goedel-Prover-V2-8B"
SUMMARY_RELATIVE_PATH = Path("finalized_answers/summary.json")

CATEGORIES = (
    ("AIMEI", "AIMEI_"),
    ("AIMEII", "AIMEII_"),
    ("HMMT", "HMMT_"),
    ("APEX", "APEX_"),
    ("putnam", "putnam_"),
)


@dataclass
class Counts:
    correct: int = 0
    total: int = 0

    @property
    def accuracy(self) -> float | None:
        if self.total == 0:
            return None
        return self.correct / self.total


def load_summary(summary_path: Path) -> list[dict[str, Any]]:
    with summary_path.open() as f:
        records = json.load(f)

    if not isinstance(records, list):
        raise TypeError(f"{summary_path} must contain a JSON list")

    for index, record in enumerate(records):
        if not isinstance(record, dict):
            raise TypeError(f"{summary_path} record {index} is not a JSON object")

    return records


def is_true(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value.strip().lower() == "true"
    return False


def category_for(problem_name: str) -> str | None:
    for category, marker in CATEGORIES:
        if marker in problem_name:
            return category
    return None


def discover_experiment_dirs() -> list[Path]:
    return sorted(
        path
        for path in OUTPUT_ROOT.iterdir()
        if path.is_dir() and FOLDER_SUBSTRING in path.name
    )


def summarize_folder(summary_path: Path) -> tuple[dict[str, Counts], int]:
    counts = {category: Counts() for category, _ in CATEGORIES}
    unmatched = 0

    for record in load_summary(summary_path):
        problem_name = str(record.get("name", ""))
        category = category_for(problem_name)
        if category is None:
            unmatched += 1
            continue

        counts[category].total += 1
        if is_true(record.get("is_equivalent")):
            counts[category].correct += 1

    return counts, unmatched


def format_accuracy(counts: Counts) -> str:
    if counts.accuracy is None:
        return "N/A"
    return f"{counts.accuracy:.4f} ({counts.accuracy * 100:.2f}%)"


def format_experiment_label(experiment_dir: Path) -> str:
    parts = experiment_dir.name.split("_")
    if len(parts) < 3:
        return experiment_dir.name

    dataset, model, baseline = parts[:3]
    return f"dataset: {dataset}, model: {model}, baseline: {baseline}"


def build_report() -> str:
    experiment_dirs = discover_experiment_dirs()
    processed: list[tuple[Path, dict[str, Counts], int]] = []
    skipped: list[Path] = []

    for experiment_dir in experiment_dirs:
        summary_path = experiment_dir / SUMMARY_RELATIVE_PATH
        if not summary_path.exists():
            skipped.append(experiment_dir)
            continue

        counts, unmatched = summarize_folder(summary_path)
        processed.append((experiment_dir, counts, unmatched))

    lines = []

    for experiment_dir, counts_by_category, unmatched in processed:
        lines.append(format_experiment_label(experiment_dir))

        classified_total = Counts()
        for category, _ in CATEGORIES:
            counts = counts_by_category[category]
            classified_total.correct += counts.correct
            classified_total.total += counts.total
            if counts.total == 0:
                continue
            lines.append(
                f"  {category}: {counts.correct}/{counts.total} "
                f"accuracy={format_accuracy(counts)}"
            )

        lines.append(
            f"  overall: "
            f"{classified_total.correct}/{classified_total.total} "
            f"accuracy={format_accuracy(classified_total)}"
        )
        if unmatched:
            lines.append(f"  unmatched_records: {unmatched}")
        lines.append("")

    if skipped:
        lines.append("Skipped folders without finalized answer summary")
        for experiment_dir in skipped:
            lines.append(f"  {format_experiment_label(experiment_dir)}")
        lines.append("")

    if not processed:
        lines.append("No matching folders with finalized answer summaries were found.")
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def main() -> None:
    report = build_report()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(report)
    print(report, end="")
    print(f"Saved report to {REPORT_PATH}")


if __name__ == "__main__":
    main()
