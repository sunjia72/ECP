#!/bin/bash
set -e

# ================= DEFAULT CONFIGURATION =================

CPU_COUNT_DEFAULT="$(python - <<'PY'
import os
print(os.cpu_count() or 1)
PY
)"

MODEL_PATH_DEFAULT="Goedel-LM/Goedel-Prover-V2-8B"
DATA_PATH_DEFAULT="dataset/test.jsonl"

GPUS_DEFAULT=4
CPUS_DEFAULT="${CPU_COUNT_DEFAULT}"
NODES_DEFAULT=1
NUM_SAMPLES_INITIAL_DEFAULT=128
NUM_SAMPLES_CORRECTION_DEFAULT=1
MAX_CORRECTION_ROUNDS_DEFAULT=20

TEMPERATURE_DEFAULT=1.0
MAX_MODEL_LEN_DEFAULT=30000
INFERENCE_HANDLER_DEFAULT="dpskcot"
COMMERCIAL_PARALLEL_DEFAULT="${COMMERCIAL_PARALLEL:-${CPU_COUNT_DEFAULT}}"

# The user can optionally override BASE_OUTPUT_DIR; if not, we compute one.
BASE_OUTPUT_DIR_DEFAULT=""

# ================= ARGUMENT PARSING =================

usage() {
    echo "Usage: $0 [options]"
    echo
    echo "Options (all optional, defaults shown in brackets):"
    echo "  -m  MODEL_PATH             [${MODEL_PATH_DEFAULT}]"
    echo "  -d  DATA_PATH              [${DATA_PATH_DEFAULT}]"
    echo "  -o  BASE_OUTPUT_DIR        [auto from DATA_PATH]"
    echo "  -g  GPUS                   [${GPUS_DEFAULT}]"
    echo "  -c  CPUS                   [${CPUS_DEFAULT}]"
    echo "  -i  NUM_SAMPLES_INITIAL    [${NUM_SAMPLES_INITIAL_DEFAULT}]"
    echo "  -r  NUM_SAMPLES_CORRECTION [${NUM_SAMPLES_CORRECTION_DEFAULT}]"
    echo "  -R  MAX_CORRECTION_ROUNDS  [${MAX_CORRECTION_ROUNDS_DEFAULT}]"
    echo "  -P  COMMERCIAL_PARALLEL    [${COMMERCIAL_PARALLEL_DEFAULT}]"
    echo "  -a  Enable outer existential witness admissibility check during compilation"
    echo "  -h  Show this help"
    exit 1
}

is_commercial_model() {
  local model_lc
  model_lc=$(python - "$1" <<'PY'
import sys
print((sys.argv[1] if len(sys.argv) > 1 else "").strip().lower())
PY
)
  case "$model_lc" in
    gpt-5*|openai/*|google/*|qwen/*|anthropic/*|deepseek/*|meta-llama/*|mistralai/*|x-ai/*|cohere/*|moonshotai/*)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}
is_empty_json_list() {
  # returns 0 (true) if file exists and JSON content is [] (possibly with whitespace/newlines)
  local f="$1"
  if [ ! -f "$f" ]; then
    return 1
  fi

  python - "$f" <<'PY'
import json, sys
p = sys.argv[1]
try:
    with open(p, "r") as fp:
        obj = json.load(fp)
    ok = isinstance(obj, list) and len(obj) == 0
    sys.exit(0 if ok else 1)
except Exception:
    sys.exit(1)
PY
}

json_list_len() {
  local f="$1"
  if [ ! -f "$f" ]; then
    return 1
  fi

  python - "$f" <<'PY'
import json, sys
p = sys.argv[1]
try:
    with open(p, "r", encoding="utf-8") as fp:
        obj = json.load(fp)
    if not isinstance(obj, list):
        raise TypeError(type(obj).__name__)
    print(len(obj))
except Exception:
    sys.exit(1)
PY
}

json_bad_inference_count() {
  local f="$1"
  if [ ! -f "$f" ]; then
    return 1
  fi

  python - "$f" <<'PY'
import json, sys
p = sys.argv[1]
try:
    with open(p, "r", encoding="utf-8") as fp:
        obj = json.load(fp)
    if not isinstance(obj, list):
        raise TypeError(type(obj).__name__)
    bad = 0
    for row in obj:
        if not isinstance(row, dict):
            bad += 1
            continue
        if not row.get("problem_id"):
            bad += 1
    print(bad)
except Exception:
    sys.exit(1)
PY
}

json_terminal_inference_failure_count() {
  local f="$1"
  if [ ! -f "$f" ]; then
    return 1
  fi

  python - "$f" <<'PY'
import json, sys

def empty_text(value):
    return not isinstance(value, str) or not value.strip()

def empty_code(value):
    if value is None:
        return True
    if not isinstance(value, str):
        return True
    text = value.strip()
    return not text or text.lower() in {"none", "null", "nan"}

p = sys.argv[1]
try:
    with open(p, "r", encoding="utf-8") as fp:
        obj = json.load(fp)
    if not isinstance(obj, list):
        raise TypeError(type(obj).__name__)
    failed = 0
    for row in obj:
        if not isinstance(row, dict):
            continue
        if row.get("inference_error"):
            failed += 1
            continue
        if "model_output" in row and empty_text(row.get("model_output")):
            failed += 1
            continue
        if "full_code" in row and empty_code(row.get("full_code")):
            failed += 1
    print(failed)
except Exception:
    sys.exit(1)
PY
}

jsonl_record_len() {
  local f="$1"
  if [ ! -f "$f" ]; then
    return 1
  fi

  python - "$f" <<'PY'
import json, sys
p = sys.argv[1]
n = 0
try:
    with open(p, "r", encoding="utf-8") as fp:
        for line in fp:
            if not line.strip():
                continue
            json.loads(line)
            n += 1
    print(n)
except Exception:
    sys.exit(1)
PY
}

inference_output_is_complete() {
  local round_idx="$1"
  local done_flag="$2"
  local records_f="$3"
  local codes_f="$4"
  if [ ! -f "$done_flag" ] || [ ! -f "$records_f" ] || [ ! -f "$codes_f" ]; then
    return 1
  fi

  local records_count
  local codes_count
  records_count=$(json_list_len "$records_f") || return 1
  codes_count=$(json_list_len "$codes_f") || return 1

  if [ "$records_count" -ne "$codes_count" ]; then
    echo "[pipeline] Stale/incomplete inference output: records=${records_count}, codes=${codes_count}" >&2
    return 1
  fi

  local bad_records_count
  local bad_codes_count
  bad_records_count=$(json_bad_inference_count "$records_f") || return 1
  bad_codes_count=$(json_bad_inference_count "$codes_f") || return 1
  if [ "$bad_records_count" -gt 0 ] || [ "$bad_codes_count" -gt 0 ]; then
    echo "[pipeline] Malformed inference output: bad records=${bad_records_count}, bad codes=${bad_codes_count}" >&2
    return 1
  fi

  local terminal_failed_records_count
  local terminal_failed_codes_count
  terminal_failed_records_count=$(json_terminal_inference_failure_count "$records_f") || return 1
  terminal_failed_codes_count=$(json_terminal_inference_failure_count "$codes_f") || return 1
  if [ "$terminal_failed_records_count" -gt 0 ] || [ "$terminal_failed_codes_count" -gt 0 ]; then
    echo "[pipeline] Inference output has terminal failed sample(s): records=${terminal_failed_records_count}, codes=${terminal_failed_codes_count}; continuing." >&2
  fi

  if [ "$round_idx" -eq 0 ]; then
    local data_count
    local expected_count
    data_count=$(jsonl_record_len "$DATA_PATH") || return 1
    expected_count=$((data_count * NUM_SAMPLES))
    if [ "$expected_count" -eq 0 ] && [ "$records_count" -eq 0 ] && [ "$codes_count" -eq 0 ]; then
      return 0
    fi
    if [ "$records_count" -ge "$expected_count" ] && [ "$codes_count" -ge "$expected_count" ]; then
      return 0
    fi
    echo "[pipeline] Stale/incomplete inference output: expected rows=${expected_count}, records=${records_count}, codes=${codes_count}" >&2
    return 1
  fi

  return 0
}

compile_output_is_complete() {
  local input_f="$1"
  local output_f="$2"
  local require_witness_check="${3:-0}"
  if [ ! -f "$output_f" ]; then
    return 1
  fi

  local input_count
  local output_count
  input_count=$(json_list_len "$input_f") || return 1
  output_count=$(json_list_len "$output_f") || return 1

  if [ "$input_count" -eq 0 ] && [ "$output_count" -eq 0 ]; then
    return 0
  fi

  if [ "$input_count" -gt 0 ] && [ "$output_count" -ge "$input_count" ]; then
    if [ "$require_witness_check" -eq 1 ]; then
      python - "$output_f" <<'PY'
import json, sys
p = sys.argv[1]
try:
    with open(p, "r", encoding="utf-8") as f:
        rows = json.load(f)
    ok = isinstance(rows, list) and all(
        isinstance(row, dict) and row.get("witness_admissibility_check_enabled") is True
        for row in rows
    )
    sys.exit(0 if ok else 1)
except Exception:
    sys.exit(1)
PY
      return $?
    fi
    return 0
  fi

  echo "[pipeline] Stale/incomplete compilation output: input rows=${input_count}, output rows=${output_count}" >&2
  return 1
}



# Start with defaults
MODEL_PATH="$MODEL_PATH_DEFAULT"
DATA_PATH="$DATA_PATH_DEFAULT"
BASE_OUTPUT_DIR="$BASE_OUTPUT_DIR_DEFAULT"
GPUS="$GPUS_DEFAULT"
CPUS="$CPUS_DEFAULT"
NODES="$NODES_DEFAULT"
NUM_SAMPLES_INITIAL="$NUM_SAMPLES_INITIAL_DEFAULT"
NUM_SAMPLES_CORRECTION="$NUM_SAMPLES_CORRECTION_DEFAULT"
MAX_CORRECTION_ROUNDS="$MAX_CORRECTION_ROUNDS_DEFAULT"
TEMPERATURE="$TEMPERATURE_DEFAULT"
MAX_MODEL_LEN="$MAX_MODEL_LEN_DEFAULT"
INFERENCE_HANDLER="$INFERENCE_HANDLER_DEFAULT"
COMMERCIAL_PARALLEL="$COMMERCIAL_PARALLEL_DEFAULT"
ENABLE_WITNESS_ADMISSIBILITY_CHECK=0

# Parse flags
while getopts "m:d:o:g:c:i:r:R:N:M:P:ah" opt; do
    case "$opt" in
        m) MODEL_PATH="$OPTARG" ;;
        d) DATA_PATH="$OPTARG" ;;
        o) BASE_OUTPUT_DIR="$OPTARG" ;;
        g) GPUS="$OPTARG" ;;
        c) CPUS="$OPTARG" ;;
        N) NODES="$OPTARG" ;;
        i) NUM_SAMPLES_INITIAL="$OPTARG" ;;
        r) NUM_SAMPLES_CORRECTION="$OPTARG" ;;
        R) MAX_CORRECTION_ROUNDS="$OPTARG" ;;
        M) MAX_MODEL_LEN="$OPTARG" ;;
        P) COMMERCIAL_PARALLEL="$OPTARG" ;;
        a) ENABLE_WITNESS_ADMISSIBILITY_CHECK=1 ;;
        h) usage ;;
        *) usage ;;
    esac
done
shift $((OPTIND-1))

# If BASE_OUTPUT_DIR not provided, build a reasonable default
if [ -z "$BASE_OUTPUT_DIR" ]; then
    DATA_NAME=$(basename "$DATA_PATH")
    DATA_NAME="${DATA_NAME%.*}"  # strip extension
    BASE_OUTPUT_DIR="results/goedelv2_${DATA_NAME}_${NUM_SAMPLES_CORRECTION}correction_${NUM_SAMPLES_INITIAL}samples_restart"
fi

TIMESTAMP=$(date +%Y%m%d_%H%M%S)

echo "Configuration:"
echo "  MODEL_PATH            = ${MODEL_PATH}"
echo "  DATA_PATH             = ${DATA_PATH}"
echo "  BASE_OUTPUT_DIR       = ${BASE_OUTPUT_DIR}"
echo "  GPUS per node         = ${GPUS}"
echo "  CPUS                  = ${CPUS}"
echo "  Physical NODES        = ${NODES}"
echo "  NUM_SAMPLES_INITIAL   = ${NUM_SAMPLES_INITIAL}"
echo "  NUM_SAMPLES_CORRECTION= ${NUM_SAMPLES_CORRECTION}"
echo "  MAX_CORRECTION_ROUNDS = ${MAX_CORRECTION_ROUNDS}"
echo "  INFERENCE_HANDLER     = ${INFERENCE_HANDLER}"
echo "  TEMPERATURE           = ${TEMPERATURE}"
echo "  MAX_MODEL_LEN         = ${MAX_MODEL_LEN}"
echo "  COMMERCIAL_PARALLEL   = ${COMMERCIAL_PARALLEL}"
echo "  WITNESS_ADMISSIBILITY = ${ENABLE_WITNESS_ADMISSIBILITY_CHECK}"
echo

COMMERCIAL_INFERENCE=0
PIPELINE_NODES="$NODES"
if is_commercial_model "$MODEL_PATH"; then
    COMMERCIAL_INFERENCE=1
    PIPELINE_NODES=1
    echo "[pipeline] Commercial prover model detected; using src.goedel.inference_commercial."
    echo "[pipeline] Commercial inference/compilation is forced to single-node mode."
fi

# --- Main Loop ---
for round in $(seq 0 $MAX_CORRECTION_ROUNDS); do
    echo
    echo "===================================================="
    echo "===============   Starting Round ${round}   ==============="
    echo "===================================================="

    # Round-specific suffix and paths
    SUFFIX=""
    if [ "$round" -gt 0 ]; then
        SUFFIX="_corr${round}"
    fi

    INFERENCE_OUTPUT_FILE="${BASE_OUTPUT_DIR}/to_inference_codes${SUFFIX}.json"
    FULL_RECORDS_FILE="${BASE_OUTPUT_DIR}/full_records${SUFFIX}.json"
    COMPILE_OUTPUT_FILE="${BASE_OUTPUT_DIR}/code_compilation_repl${SUFFIX}.json"
    SUMMARY_OUTPUT_DIR="${BASE_OUTPUT_DIR}/summary_round_${round}"
    SUMMARY_META_FILE="${SUMMARY_OUTPUT_DIR}/meta_summarize.json"

    # Decide N for this round
    if [ "$round" -eq 0 ]; then
        NUM_SAMPLES=$NUM_SAMPLES_INITIAL
    else
        NUM_SAMPLES=$NUM_SAMPLES_CORRECTION
    fi

    # --- Step 1: Inference ---
    echo
    echo "--- [Step 1/3] Inference Phase (Round ${round}) ---"

    # New: a "done" flag so we don't skip just because partial JSONs exist.
    INFERENCE_DONE_FLAG="${BASE_OUTPUT_DIR}/inference_round_${round}_DONE.flag"

    if inference_output_is_complete "$round" "$INFERENCE_DONE_FLAG" "$FULL_RECORDS_FILE" "$INFERENCE_OUTPUT_FILE"; then
        echo "Inference already completed for round ${round} (found ${INFERENCE_DONE_FLAG}):"
        echo "  ${INFERENCE_OUTPUT_FILE}"
        echo "  ${FULL_RECORDS_FILE}"
        echo "Skipping inference for this round."
    else
        if [ -f "$INFERENCE_DONE_FLAG" ]; then
            echo "Existing inference output is stale or incomplete; resuming/rerunning missing samples:"
            echo "  ${INFERENCE_OUTPUT_FILE}"
            echo "  ${FULL_RECORDS_FILE}"
        fi
        echo "Running inference for round ${round}..."

        if [ "$round" -eq 0 ]; then
            # Round 0: Create proofs from the initial dataset
            INPUT_ARG="--input_path ${DATA_PATH}"
            PREV_RUN_ARG=""  # No previous run output is needed
        else
            # Correction Round (> 0): Correct proofs based on failures from the previous round
            INPUT_ARG=""  # Initial dataset is not needed
            PREV_RUN_ARG="--previous_run_output_dir ${BASE_OUTPUT_DIR}"
        fi

        if [ "$COMMERCIAL_INFERENCE" -eq 1 ]; then
            INFERENCE_CMD="python -m src.goedel.inference_commercial \
                --model_path ${MODEL_PATH} \
                --output_dir ${BASE_OUTPUT_DIR} \
                --n ${NUM_SAMPLES} \
                --node 1 \
                --inference_handler ${INFERENCE_HANDLER} \
                --correction_round ${round} \
                --max_model_len ${MAX_MODEL_LEN} \
                --temp ${TEMPERATURE} \
                --parallel ${COMMERCIAL_PARALLEL} \
                ${INPUT_ARG} \
                ${PREV_RUN_ARG}"
        else
            INFERENCE_CMD="python -m src.goedel.inference \
                --model_path ${MODEL_PATH} \
                --output_dir ${BASE_OUTPUT_DIR} \
                --n ${NUM_SAMPLES} \
                --gpu ${GPUS} \
                --node ${NODES} \
                --inference_handler ${INFERENCE_HANDLER} \
                --correction_round ${round} \
                --max_model_len ${MAX_MODEL_LEN} \
                --temp ${TEMPERATURE} \
                ${INPUT_ARG} \
                ${PREV_RUN_ARG}"
        fi

        echo "Executing command:"
        echo "${INFERENCE_CMD}"
        ${INFERENCE_CMD}

        # Check if the inference output files exist
        # New: mark this round as fully done, then validate against the requested sample count.
        touch "${INFERENCE_DONE_FLAG}"
        if ! inference_output_is_complete "$round" "$INFERENCE_DONE_FLAG" "$FULL_RECORDS_FILE" "$INFERENCE_OUTPUT_FILE"; then
            echo "Error: Inference outputs are missing or incomplete for requested configuration! Terminating."
            exit 1
        fi
        echo "Inference complete for round ${round}."
        echo "  Inference codes: ${INFERENCE_OUTPUT_FILE}"
        echo "  Full records:    ${FULL_RECORDS_FILE}"
        echo "  Done flag:       ${INFERENCE_DONE_FLAG}"
    fi

    if [ "$round" -gt 0 ]; then
        if is_empty_json_list "${INFERENCE_OUTPUT_FILE}" && is_empty_json_list "${FULL_RECORDS_FILE}"; then
            echo
            echo "[pipeline] Round ${round}: no remaining failures (inference outputs are empty)."
            echo "[pipeline] Stopping refinement loop and jumping to final summary."
            break
        fi
    fi
    # --- Step 2: Compilation ---
    echo
    echo "--- [Step 2/3] Compilation Phase (Round ${round}) ---"

    if compile_output_is_complete "$INFERENCE_OUTPUT_FILE" "$COMPILE_OUTPUT_FILE" "$ENABLE_WITNESS_ADMISSIBILITY_CHECK"; then
        echo "Compilation output already exists for round ${round}:"
        echo "  $COMPILE_OUTPUT_FILE"
        echo "Skipping compilation for this round."
    else
        if [ -f "$COMPILE_OUTPUT_FILE" ]; then
            echo "Existing compilation output is stale or incomplete; rerunning:"
            echo "  $COMPILE_OUTPUT_FILE"
        fi
        echo "Running compilation for round ${round}..."

        COMPILE_EXTRA_ARGS=""
        if [ "$ENABLE_WITNESS_ADMISSIBILITY_CHECK" -eq 1 ]; then
            COMPILE_EXTRA_ARGS="--enable_witness_admissibility_check --metadata_path ${DATA_PATH}"
        fi

        COMPILE_CMD="python -m src.goedel.compile \
            --input_path ${INFERENCE_OUTPUT_FILE} \
            --output_path ${COMPILE_OUTPUT_FILE} \
            --cpu ${CPUS} \
            --node ${PIPELINE_NODES} \
            ${COMPILE_EXTRA_ARGS}"

        echo "Executing command:"
        echo "${COMPILE_CMD}"
        ${COMPILE_CMD}

        # Check if the compilation output file exists
        if ! compile_output_is_complete "$INFERENCE_OUTPUT_FILE" "$COMPILE_OUTPUT_FILE" "$ENABLE_WITNESS_ADMISSIBILITY_CHECK"; then
            echo "Error: Compilation output file ${COMPILE_OUTPUT_FILE} is missing or incomplete! Terminating."
            exit 1
        fi
        echo "Compilation complete for round ${round}."
        echo "  Compilation output: ${COMPILE_OUTPUT_FILE}"
    fi

    # --- Step 3: Summarization ---
    echo
    echo "--- [Step 3/3] Summarization Phase (Round ${round}) ---"

    mkdir -p "$SUMMARY_OUTPUT_DIR"


    echo "Running summarization for round ${round}..."

    SUMMARY_CMD="python -m src.goedel.summarize \
        --input_path ${COMPILE_OUTPUT_FILE} \
        --full_record_path ${FULL_RECORDS_FILE} \
        --output_dir ${SUMMARY_OUTPUT_DIR}"

    echo "Executing command:"
    echo "${SUMMARY_CMD}"
    ${SUMMARY_CMD}
    echo "Summary reports generated for round ${round} in: ${SUMMARY_OUTPUT_DIR}"


done

# ---------- NEW: Final aggregated summary across all rounds ----------
echo
echo "===================================================="
echo "Generating final aggregated summary across all rounds (if needed)..."
echo "===================================================="

FINAL_SUMMARY_DIR="${BASE_OUTPUT_DIR}/final_summary"
FINAL_SUMMARY_JSON="${FINAL_SUMMARY_DIR}/final_summary.json"

mkdir -p "${FINAL_SUMMARY_DIR}"


FINAL_SUMMARY_CMD="python -m src.goedel.final_summarize \
    --base_output_dir ${BASE_OUTPUT_DIR} \
    --max_round ${MAX_CORRECTION_ROUNDS} \
    --output_dir ${FINAL_SUMMARY_DIR}"

echo "Executing command:"
echo "${FINAL_SUMMARY_CMD}"
${FINAL_SUMMARY_CMD}
echo "Final summary generated in: ${FINAL_SUMMARY_DIR}"


echo
echo "===================================================="
echo "All rounds completed (with resume support)."
echo "Final results are saved in the directory: ${BASE_OUTPUT_DIR}"
echo "===================================================="
