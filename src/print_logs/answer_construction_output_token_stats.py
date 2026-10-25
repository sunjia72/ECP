import json
from pathlib import Path



DEFAULT_INPUTS = {
    "matharena_Qwen3-32B_mcp_Goedel-Prover-V2-8B":  "output/matharena_Qwen3-32B_mcp_Goedel-Prover-V2-8B/finalized_answers/summary.json",
    "matharena_Qwen3-32B_cot_Goedel-Prover-V2-8B":  "output/matharena_Qwen3-32B_cot_Goedel-Prover-V2-8B/finalized_answers/summary.json",
    "putnam_Qwen3-32B_mcp_Goedel-Prover-V2-8B":  "output/putnam_Qwen3-32B_mcp_Goedel-Prover-V2-8B/finalized_answers/summary.json",
    "putnam_Qwen3-32B_cot_Goedel-Prover-V2-8B":  "output/putnam_Qwen3-32B_cot_Goedel-Prover-V2-8B/finalized_answers/summary.json",
    "matharena_gpt-5_mcp_Goedel-Prover-V2-8B":  "output/matharena_gpt-5_mcp_Goedel-Prover-V2-8B/finalized_answers/summary.json",
    "matharena_gpt-5_cot_Goedel-Prover-V2-8B":  "output/matharena_gpt-5_cot_Goedel-Prover-V2-8B/finalized_answers/summary.json",
    "putnam_gpt-5_mcp_Goedel-Prover-V2-8B":  "output/putnam_gpt-5_mcp_Goedel-Prover-V2-8B/finalized_answers/summary.json",
    "putnam_gpt-5_cot_Goedel-Prover-V2-8B":  "output/putnam_gpt-5_cot_Goedel-Prover-V2-8B/finalized_answers/summary.json",
}
FIELD_NAME = "answer_construction_output_tokens"


def load_summary_records(input_path: str | Path) -> list[dict]:
    input_path = Path(input_path)
    with input_path.open() as f:
        records = json.load(f)

    if not isinstance(records, list):
        raise TypeError(f"{input_path} must contain a JSON list")

    for index, record in enumerate(records):
        if not isinstance(record, dict):
            raise TypeError(f"{input_path} record {index} is not a JSON object")

    return records


def compute_stats(input_path: str | Path) -> dict[str, float | int]:
    total = 0
    count = 0

    for index, record in enumerate(load_summary_records(input_path)):
        if FIELD_NAME not in record:
            raise KeyError(f"Missing {FIELD_NAME} in record {index}")

        total += int(record[FIELD_NAME])
        count += 1

    average = total / count if count else 0.0
    return {
        "count": count,
        "sum": total,
        "average": average,
    }


def main() -> None:
    for label, input_path in DEFAULT_INPUTS.items():
        stats = compute_stats(input_path)
        print(f"{label}: {stats}")


if __name__ == "__main__":
    main()
