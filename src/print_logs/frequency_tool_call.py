import json
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.ticker import PercentFormatter


DEFAULT_INPUTS = {
    "matharena": "output/matharena_gpt-5_mcp_Goedel-Prover-V2-8B/finalized_answers/summary.json",
    "putnam": "output/putnam_gpt-5_mcp_Goedel-Prover-V2-8B/finalized_answers/summary.json",
}
DEFAULT_OUTPUT_DIR = Path("src/print_logs/frequency")
FIELD_NAME = "answer_construction_tool_calls"
X_AXIS_LABEL = "Number of Tool Calls"
STATS_OUTPUT_PATH = DEFAULT_OUTPUT_DIR / f"{FIELD_NAME}_stats.json"
PLOT_OUTPUT_PATH = DEFAULT_OUTPUT_DIR / f"{FIELD_NAME}_histogram.pdf"

BUCKETS = ["0", "1", "2", "3", "4", "5", "6+"]
CATEGORIES = (
    ("AIMEI", "AIMEI_"),
    ("AIMEII", "AIMEII_"),
    ("HMMT", "HMMT_"),
    ("APEX", "APEX_"),
    ("putnam", "putnam_"),
)


def category_for(problem_name: str) -> str | None:
    for category, marker in CATEGORIES:
        if marker in problem_name:
            return category
    return None


def bucket_count(value: int) -> str:
    if value >= 6:
        return "6+"
    if value < 0:
        raise ValueError(f"{X_AXIS_LABEL} must be nonnegative, got {value}")
    return str(value)


def summarize_tool_calls(
    record_count: int, total_tool_calls: int
) -> dict[str, int | float]:
    average_tool_calls = total_tool_calls / record_count if record_count else 0.0
    return {
        "record_count": record_count,
        "total_tool_calls": total_tool_calls,
        "average_tool_calls_per_file": average_tool_calls,
    }


def load_summary_records(input_path: Path) -> list[dict]:
    with input_path.open() as f:
        records = json.load(f)

    if not isinstance(records, list):
        raise TypeError(f"{input_path} must contain a JSON list")

    for index, record in enumerate(records):
        if not isinstance(record, dict):
            raise TypeError(f"{input_path} record {index} is not a JSON object")

    return records


def load_tool_call_stats(
    input_path: str | Path,
) -> tuple[dict[str, int], dict[str, object]]:
    input_path = Path(input_path)
    frequency = {bucket: 0 for bucket in BUCKETS}
    category_counters = {
        category: {"record_count": 0, "total_tool_calls": 0}
        for category, _ in CATEGORIES
    }
    record_count = 0
    total_tool_calls = 0
    unmatched_record_count = 0

    for index, record in enumerate(load_summary_records(input_path)):
        if FIELD_NAME not in record:
            raise KeyError(f"Missing {FIELD_NAME} in record {index}")

        tool_calls = int(record[FIELD_NAME])
        frequency[bucket_count(tool_calls)] += 1
        record_count += 1
        total_tool_calls += tool_calls

        problem_name = str(record.get("name", ""))
        category = category_for(problem_name)
        if category is None:
            unmatched_record_count += 1
            continue

        category_counters[category]["record_count"] += 1
        category_counters[category]["total_tool_calls"] += tool_calls

    category_stats = {
        category: summarize_tool_calls(
            counter["record_count"], counter["total_tool_calls"]
        )
        for category, counter in category_counters.items()
    }
    stats = summarize_tool_calls(record_count, total_tool_calls)
    stats["category_tool_calls"] = category_stats
    stats["unmatched_record_count"] = unmatched_record_count
    return frequency, stats


def plot_grouped_frequency(
    frequencies_by_label: dict[str, dict[str, int]], output_path: Path
) -> None:
    output_path.parent.mkdir(parents=True, exist_ok=True)

    labels = BUCKETS
    series_labels = list(frequencies_by_label)
    series_count = len(series_labels)
    x_positions = list(range(len(labels)))
    bar_width = 0.8 / series_count

    fig, ax = plt.subplots(figsize=(8.5, 5))
    colors = ["steelblue", "darkorange"]

    for series_index, series_label in enumerate(series_labels):
        counts = [frequencies_by_label[series_label][label] for label in labels]
        total_count = sum(counts)
        percentages = [
            count / total_count * 100 if total_count else 0.0 for count in counts
        ]
        offset = (series_index - (series_count - 1) / 2) * bar_width
        bar_positions = [x + offset for x in x_positions]
        bars = ax.bar(
            bar_positions,
            percentages,
            width=bar_width * 0.9,
            label=series_label,
            color=colors[series_index % len(colors)],
            edgecolor="black",
            linewidth=0.8,
        )

        for bar, percentage in zip(bars, percentages):
            ax.text(
                bar.get_x() + bar.get_width() / 2,
                bar.get_height(),
                f"{percentage:.1f}%",
                ha="center",
                va="bottom",
                fontsize=10,
            )

    ax.set_xlabel(X_AXIS_LABEL)
    ax.set_ylabel("Percentage of Problems")
    ax.set_xticks(x_positions)
    ax.set_xticklabels(labels)
    ax.set_axisbelow(True)
    ax.yaxis.set_major_formatter(PercentFormatter(xmax=100))
    ax.yaxis.grid(True, linestyle="--", alpha=0.35)
    ax.legend(frameon=False)

    fig.tight_layout()
    fig.savefig(output_path, bbox_inches="tight", dpi=300)
    plt.close(fig)


def save_stats(stats_by_label: dict[str, dict[str, object]]) -> None:
    STATS_OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    STATS_OUTPUT_PATH.write_text(json.dumps(stats_by_label, indent=2) + "\n")


def main() -> None:
    stats_by_label: dict[str, dict[str, object]] = {}
    frequencies_by_label: dict[str, dict[str, int]] = {}

    for label, input_path in DEFAULT_INPUTS.items():
        frequency, stats = load_tool_call_stats(input_path)

        frequencies_by_label[label] = frequency
        stats_by_label[label] = {
            "input_path": str(input_path),
            "frequency": frequency,
            **stats,
        }

        print(f"{label}: frequency={frequency}, stats={stats}")

    plot_grouped_frequency(frequencies_by_label, PLOT_OUTPUT_PATH)
    print(f"Saved histogram to {PLOT_OUTPUT_PATH}")

    save_stats(stats_by_label)
    print(f"Saved stats to {STATS_OUTPUT_PATH}")


if __name__ == "__main__":
    main()
