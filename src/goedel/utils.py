import re
import pandas as pd
import numpy as np
import json
from jload import jload, jsave
import os
import copy

# ----------------------------
# Feedback construction helpers
# ----------------------------

MAX_FEEDBACK_CODE_CHARS = 6000
MAX_CORRECTION_ERROR_CHARS = 12000
MAX_CORRECTION_PREV_CODE_CHARS = 6000


def truncate_middle_text(text, max_chars, label="text"):
    text = "" if text is None else str(text)
    if max_chars <= 0 or len(text) <= max_chars:
        return text
    marker = f"\n\n-- [{label} truncated: omitted {len(text) - max_chars} characters]\n\n"
    keep = max(0, max_chars - len(marker))
    head = keep // 2
    tail = keep - head
    tail_text = text[-tail:].lstrip() if tail else ""
    return text[:head].rstrip() + marker + tail_text


def compact_correction_feedback(text):
    return truncate_middle_text(text, MAX_CORRECTION_ERROR_CHARS, "diagnostic feedback")


def compact_previous_code(text):
    if text in ("None", None):
        return "None"
    return truncate_middle_text(text, MAX_CORRECTION_PREV_CODE_CHARS, "previous Lean attempt")

def _highlight_span(code_lines, start_line, start_col, end_line, end_col, truncate_middle=False, show_line_window=6):
    """
    Build a small code excerpt with <error>...</error> highlighting for a span.
    Robust to out-of-range positions.
    """
    n_lines = len(code_lines)
    start_line = max(0, min(start_line, n_lines - 1))
    end_line = max(0, min(end_line, n_lines - 1))

    excerpt = ""
    # Context above
    for ii in range(max(0, start_line - 4), start_line):
        excerpt += f"{code_lines[ii]}\n"

    # Error lines
    if start_line == end_line:
        line = code_lines[start_line]
        start_col = max(0, min(start_col, len(line)))
        end_col = max(start_col, min(end_col, len(line)))
        excerpt += line[:start_col] + "<error>" + line[start_col:end_col] + "</error>" + line[end_col:] + "\n"
    else:
        # first line
        first_line = code_lines[start_line]
        start_col = max(0, min(start_col, len(first_line)))
        excerpt += first_line[:start_col] + "<error>" + first_line[start_col:] + "\n"

        # middle lines
        if truncate_middle and end_line - start_line - 1 > show_line_window:
            for j in range(start_line + 1, start_line + 1 + show_line_window):
                excerpt += f"{code_lines[j]}\n"
            last_shown = code_lines[start_line + show_line_window]
            leading_spaces = len(last_shown) - len(last_shown.lstrip(' '))
            excerpt += "\n" + " " * leading_spaces + "... --[Truncated]-- ...\n"
        else:
            for j in range(start_line + 1, end_line):
                excerpt += f"{code_lines[j]}\n"

        # last line
        last_line = code_lines[end_line]
        end_col = max(0, min(end_col, len(last_line)))
        excerpt += last_line[:end_col] + "</error>" + last_line[end_col:] + "\n"

    # Context below
    if end_line + 1 < n_lines:
        excerpt += f"{code_lines[end_line + 1]}\n"

    return excerpt


def get_error_str(code, comp_result, error_thres=True):
    """
    Build a human-readable feedback string for the correction round.

    Supports:
      - structured `errors` (Lean diagnostics with pos/endPos/data)
      - structured `sorries` (positions of remaining `sorry`s)
      - `system_errors` (timeouts, JSON decode failures, REPL crashes)
      - empty diagnostics, but `complete == False` (still trigger retry)
    """
    # Backward compatibility: allow a list to be passed as 'errors'
    if isinstance(comp_result, list):
        comp_result = {"errors": comp_result}

    errors = comp_result.get("errors", []) or []
    sorries = comp_result.get("sorries", []) or []
    warnings = comp_result.get("warnings", []) or []
    system_errors = comp_result.get("system_errors", None)
    pass_flag = comp_result.get("pass", False)
    complete_flag = comp_result.get("complete", False)

    code_lines = code.split("\n")
    max_items = 8 if error_thres else max(len(errors), len(sorries), 64)

    parts = []
    parts.append(
        f"Compiler status: pass={bool(pass_flag)}, complete={bool(complete_flag)}."
    )

    # System errors (timeouts / JSON decode / REPL crash)
    if system_errors:
        parts.append("\nSystem error encountered (REPL/driver):\n```\n" + str(system_errors).strip() + "\n```")

    # Structured Lean errors
    if errors:
        parts.append(f"\nTop {min(len(errors), max_items)} Lean error(s) with context:")
        for i, err in enumerate(errors[:max_items], 1):
            pos = err.get("pos", {}) or {}
            endPos = err.get("endPos", None)
            start_line = max(1, pos.get("line", 1)) - 1
            start_col = max(0, pos.get("column", 0))
            if endPos is None:
                end_line = start_line
                end_col = len(code_lines[start_line]) if 0 <= start_line < len(code_lines) else 0
            else:
                end_line = max(1, endPos.get("line", start_line + 1)) - 1
                end_col = max(0, endPos.get("column", 0))

            excerpt = _highlight_span(
                code_lines, start_line, start_col, end_line, end_col,
                truncate_middle=bool(error_thres)
            )
            parts.append(f"\nError {i}:\n\nCorresponding Code:\n```lean4\n{excerpt}```\n"
                         f"\nError Message: {err.get('data', '')}\n")

        if len(errors) > max_items:
            parts.append(f"\n... [Omitted {len(errors) - max_items} additional errors] ...")

    # Sorries (incomplete proof markers)
    if sorries:
        parts.append(f"\nFound {len(sorries)} remaining `sorry` site(s) (showing up to {max_items}):")
        for i, s in enumerate(sorries[:max_items], 1):
            pos = s.get("pos", {}) or {}
            endPos = s.get("endPos", {}) or {}
            start_line = max(1, pos.get("line", 1)) - 1
            start_col = max(0, pos.get("column", 0))
            end_line = max(1, endPos.get("line", start_line + 1)) - 1
            end_col = max(0, endPos.get("column", 0))

            excerpt = _highlight_span(
                code_lines, start_line, start_col, end_line, end_col,
                truncate_middle=bool(error_thres)
            )
            goal = s.get("goal", "")
            parts.append(
                f"\nSorry {i} (goal snapshot shown if available):\n\nCorresponding Code:\n```lean4\n{excerpt}```\n"
                + (f"\nGoal:\n```\n{goal}\n```\n" if goal else "")
            )

        if len(sorries) > max_items:
            parts.append(f"\n... [Omitted {len(sorries) - max_items} additional `sorry` sites] ...")

    # If neither errors nor sorries but still incomplete, say so and highlight literal `sorry` if present
    if not errors and not sorries and not bool(complete_flag):
        marked_code = code
        if "sorry" in code:
            occurrences = [m.span() for m in re.finditer(r"\bsorry\b", code)]
            max_mark = min(5, len(occurrences)) if error_thres else len(occurrences)
            for (a, b) in reversed(occurrences[:max_mark]):
                marked_code = marked_code[:a] + "<error>sorry</error>" + marked_code[b:]
            parts.append("\nThe proof is incomplete (`complete=false`) but no structured diagnostics were captured.")
            parts.append(
                "Highlighted `sorry` occurrences in your code for reference:\n```lean4\n"
                + truncate_middle_text(marked_code, MAX_FEEDBACK_CODE_CHARS, "highlighted code")
                + "\n```"
            )
        else:
            parts.append("\nThe proof is incomplete (`complete=false`) and no structured diagnostics were captured.")

    # Useful warnings
    if warnings:
        warn_lines = []
        for w in warnings[:max_items]:
            data = w.get("data", "")
            if data:
                warn_lines.append(f"- {data}")
        if warn_lines:
            parts.append("\nCompiler warnings excerpt:\n" + "\n".join(warn_lines))

    parts.append(
        "\nPlease produce a fresh, *complete* Lean 4 proof **without any `sorry`**. "
        "Return exactly one ```lean4``` block that includes the theorem header and the finished proof."
    )

    return "\n".join(parts)


def extract_dpsk_instruction(dpsk_str):  # dpsk 7b output
    return dpsk_str.split("<｜User｜>")[1].split("<｜Assistant｜>")[0]


def extract_qwen_instruction(qwen_str):  # qwen output
    return qwen_str.split("<|im_start|>user")[1].split("<|im_end|>")[0].strip()


def _synthesize_errors_from_result(comp_result: dict, code: str) -> list:
    """
    Build a synthetic 'errors' list when the compiler did not return structured errors
    but the attempt clearly failed (incomplete, system error, timeout, etc).
    """
    synthetic = []

    # 1) Use 'sorries' if present
    for s in comp_result.get("sorries", []) or []:
        pos = s.get("pos") or {"line": 1, "column": 0}
        endPos = s.get("endPos")  # may be None
        goal = s.get("goal", "")
        synthetic.append({
            "pos": {"line": int(pos.get("line", 1)), "column": int(pos.get("column", 0))},
            "endPos": ({"line": int(endPos.get("line", 1)), "column": int(endPos.get("column", 0))} if endPos else None),
            "data": f"Incomplete proof: contains 'sorry'. Goal at this point:\n{goal}"
        })

    # 2) Attach system_errors (timeout, JSON decoder, etc.)
    sys_err = comp_result.get("system_errors")
    if sys_err:
        msg = sys_err if isinstance(sys_err, str) else json.dumps(sys_err)
        synthetic.append({
            "pos": {"line": 1, "column": 0},
            "endPos": {"line": 1, "column": 0},
            "data": f"Compiler/system error: {msg}"
        })

    # 3) Warnings that indicate 'sorry'
    for w in comp_result.get("warnings", []) or []:
        data = (w.get("data") or "")
        if "sorry" in data.lower():
            pos = w.get("pos") or {"line": 1, "column": 0}
            endPos = w.get("endPos")
            synthetic.append({
                "pos": {"line": int(pos.get("line", 1)), "column": int(pos.get("column", 0))},
                "endPos": ({"line": int(endPos.get("line", 1)), "column": int(endPos.get("column", 0))} if endPos else None),
                "data": f"Warning indicates incomplete proof: {data}"
            })

    # 4) Heuristic: code contains 'sorry'
    if not synthetic and isinstance(code, str) and ("sorry" in code):
        synthetic.append({
            "pos": {"line": 1, "column": 0},
            "endPos": None,
            "data": "Incomplete proof: source contains 'sorry', but no structured errors were returned."
        })

    # 5) Absolute fallback
    if not synthetic:
        synthetic.append({
            "pos": {"line": 1, "column": 0},
            "endPos": None,
            "data": "Unknown failure: proof did not pass/complete but no structured errors were available."
        })

    return synthetic


_UNSOLVED_MARKER = "unsolved goals"

def _errors_all_unsolved_goals(comp_result: dict) -> bool:
    errs = comp_result.get("errors") or []
    if not errs:
        return False
    for e in errs:
        if _UNSOLVED_MARKER not in (e.get("data", "").lower()):
            return False
    return True


def _name_parent_and_index(name: str):
    """
    Split attempt name into (parent_prefix, g_index).
    parent_prefix = name without the trailing `_g{idx}`; g_index is int or None.
    """
    m = re.match(r"^(.*)_g(\d+)$", name)
    if not m:
        return name, None
    return m.group(1), int(m.group(2))


def load_data_for_correction(base_output_dir_for_prev_round: str, current_correction_round_num: int,
                             num_samples_per_problem: int, base_output_template: str):
    """
    Select failed variants from the previous round and prepare inputs for the next correction round.
    Now robust to:
      - empty `errors` with `complete=false` (e.g., has `sorries`)
      - `system_errors` (timeouts/JSON failures)
      - any case where NOT (pass && complete)

    Also computes a "two consecutive unsolved goals" signal, and attaches a concise
    strategy-change hint for the next round when true.
    """
    print(f"Loading data for correction round {current_correction_round_num} from base directory: {base_output_dir_for_prev_round}")

    if current_correction_round_num == 1:
        prev_round_suffix = ""  # R0 files have no suffix
    elif current_correction_round_num > 1:
        prev_round_suffix = f"_corr{current_correction_round_num - 1}"
    else:
        print("Error: load_data_for_correction called with invalid current_correction_round_num (must be >= 1).")
        return []

    prev_inference_file = os.path.join(base_output_dir_for_prev_round, f"to_inference_codes{prev_round_suffix}.json")
    prev_compilation_file = os.path.join(base_output_dir_for_prev_round,
                                         f"code_compilation_repl{prev_round_suffix}.json")

    assert prev_inference_file, f"Error: Required previous inference file not found: {prev_inference_file}"
    assert prev_compilation_file, f"Error: Required previous compilation file not found: {prev_compilation_file}"

    to_inference_data_prev_round = jload(prev_inference_file)
    compilation_results_data_prev_round = jload(prev_compilation_file)

    if base_output_template == "qwen":
        extract_fun = extract_qwen_instruction
    elif base_output_template == "dpsk":
        extract_fun = extract_dpsk_instruction
    else:
        print("unsupported base template")
        raise Exception

    # Ensure messages_history_list exists for round-0 data
    if to_inference_data_prev_round and "messages_history_list" not in to_inference_data_prev_round[0]:
        for d in to_inference_data_prev_round:
            d["messages_history_list"] = [{"role": "user", "content": extract_fun(d["model_input"])}]

    # Map compilation results by variant name
    comp_lookup = {
        r["name"]: {"result": r.get("compilation_result", {}), "code": r.get("code", "")}
        for r in compilation_results_data_prev_round
        if isinstance(r, dict) and "name" in r
    }

    # ----------------------------
    # NEW: Detect two consecutive UNSOLVED GOALS per attempt group
    # ----------------------------
    # Group previous-round attempts by their "parent prefix" (name without trailing _g{idx})
    group_map = {}
    for name, rec in comp_lookup.items():
        parent, idx = _name_parent_and_index(name)
        if idx is None:
            continue
        group_map.setdefault(parent, []).append((idx, name, rec["result"]))

    # For each group, sort by idx and check any adjacent pair both unsolved-goals-only
    group_has_unsolved_pair = {}
    for parent, lst in group_map.items():
        lst.sort(key=lambda x: x[0])
        flags = [ _errors_all_unsolved_goals(res) for (_idx, _name, res) in lst ]
        has_pair = any(flags[i] and flags[i+1] for i in range(len(flags)-1))
        group_has_unsolved_pair[parent] = has_pair

    def _restart_hint_for_name(name: str) -> bool:
        parent, _ = _name_parent_and_index(name)
        return bool(group_has_unsolved_pair.get(parent, False))

    passed_original_ids = set()
    failed_problem_variants = {}

    for item_prev_round in to_inference_data_prev_round:
        problem_id_variant = item_prev_round.get("problem_id")
        original_problem_id = item_prev_round.get("origin_problem_id")

        if not problem_id_variant or not original_problem_id:
            continue
        id_maps = item_prev_round.get("id_maps")
        if id_maps is None:
            assert current_correction_round_num == 1, "Only first revision round accepts no id maps input. Please check your input data."
            id_maps = [{"origin_problem_id": original_problem_id}, {"generation_id": problem_id_variant}]

        if problem_id_variant not in comp_lookup:
            # Never compiled -> treat as failed; synthesize an error
            augmented_result = {"pass": False, "complete": False, "errors": [{
                "pos": {"line": 1, "column": 0},
                "endPos": None,
                "data": "Missing compilation result for this attempt; treating as failure."
            }]}
            failed_problem_variants.setdefault(original_problem_id, []).append({
                "last_problem_id": problem_id_variant,
                "origin_problem_id": original_problem_id,
                "id_maps": id_maps,
                "formal_statement": item_prev_round.get("formal_statement", ""),
                "compiled_code_that_failed_in_prev_round": item_prev_round.get("full_code", ""),
                "errors_for_compiled_code_from_prev_round": augmented_result,
                "prev_round_llm_raw_output_for_new_prompt": item_prev_round.get("model_output", ""),
                "history_messages_from_prev_round_for_new_prompt": item_prev_round.get("messages_history_list", []),
                "unsolved_goals_restart_hint": _restart_hint_for_name(problem_id_variant)
            })
            continue

        comp_data = comp_lookup[problem_id_variant]
        result = comp_data.get("result", {}) or {}
        code = comp_data.get("code", "") or ""

        is_pass = bool(result.get("pass", False))
        is_complete = bool(result.get("complete", False))

        if is_pass and is_complete:
            passed_original_ids.add(original_problem_id)
            continue

        augmented_result = copy.deepcopy(result)
        errs = list(augmented_result.get("errors") or [])
        if len(errs) == 0:
            augmented_result["errors"] = _synthesize_errors_from_result(augmented_result, code)

        failed_problem_variants.setdefault(original_problem_id, []).append({
            "last_problem_id": problem_id_variant,
            "origin_problem_id": original_problem_id,
            "id_maps": id_maps,
            "formal_statement": item_prev_round.get("formal_statement", ""),
            "compiled_code_that_failed_in_prev_round": code,
            "errors_for_compiled_code_from_prev_round": augmented_result,
            "prev_round_llm_raw_output_for_new_prompt": item_prev_round.get("model_output", ""),
            "history_messages_from_prev_round_for_new_prompt": item_prev_round.get("messages_history_list", []),
            "unsolved_goals_restart_hint": _restart_hint_for_name(problem_id_variant)
        })

    data_for_new_correction_attempts = []
    total_variants = 0
    unique_p = 0
    for original_id, variants in failed_problem_variants.items():
        if original_id in passed_original_ids:
            continue
        unique_p += 1
        total_variants += len(variants)
        for variant_item in variants:
            for i in range(num_samples_per_problem):
                new_attempt_item = copy.deepcopy(variant_item)
                problem_id_variant = variant_item["last_problem_id"]
                new_attempt_item["problem_id"] = f"{problem_id_variant}_corr{current_correction_round_num}_g{i}"
                new_attempt_item["id_maps"] = new_attempt_item["id_maps"].copy() + [
                    {f"corr{current_correction_round_num}_id": new_attempt_item["problem_id"]}
                ]
                # keep the hint flag on the new item
                data_for_new_correction_attempts.append(new_attempt_item)

    print(
        f"Correction Round {current_correction_round_num}: Identified {unique_p} unique problems with "
        f"{total_variants} failed variants. Generating {len(data_for_new_correction_attempts)} new samples for LLM inference."
    )
    return data_for_new_correction_attempts

# ----------------------------
# Lean text utilities
# ----------------------------

def remove_comments(text):  # remove comments
    text = re.sub(r'/-.*?-/', '', text, flags=re.DOTALL)
    lines = text.split('\n')
    cleaned_lines = []
    for line in lines:
        cleaned_line = line.split('--', 1)[0]
        cleaned_lines.append(cleaned_line)
    cleaned_text = '\n'.join(cleaned_lines)
    return cleaned_text.strip()

def return_theorem_to_prove(text):
    pattern = r'((?:theorem).*?:=\s*by\s*sorry)'
    match = re.search(pattern, text, re.DOTALL)
    return match.span() if match else None

def return_theorem_to_replace(text):
    pattern = r'((?:^|\s)theorem\s+.*?:=\s*by)'
    match = re.search(pattern, text, re.DOTALL)
    return match.span() if match else None

def replace_final_by_suffix(lean4_code: str, suffix: str) -> str:
    """Replace only the final theorem's proof opener.

    ECP inputs can include helper declarations/proofs before the target theorem.
    Keeping the final ``:= by`` avoids dropping those helpers while still giving
    the prover a normalized theorem to complete.
    """
    text = str(lean4_code or "").rstrip()
    matches = list(re.finditer(r":=\s*by\b", text))
    if not matches:
        return f"{text} {suffix}".rstrip()
    return f"{text[:matches[-1].start()].rstrip()} {suffix}".rstrip()

def replace_statement_in_proof(statement, proof):
    if ("apply?" in proof) or ("exact?" in proof):
        return f"**Error**, 'apply?' or 'exact?' is used, which is not allowed."
    stats_re = remove_comments(statement)
    stats_span_= return_theorem_to_prove(stats_re)
    if stats_span_ is None:
        error_app = '\n'.join(["\n"] + ['-- ' + x for x in statement.split('\n')])
        return f"**Error**, can not find 'theorem' and ':= sorry' in {error_app}"
    proof_str = remove_comments(proof)
    span = return_theorem_to_replace(proof_str)
    if span is None:
        error_app = '\n'.join(["\n"] + ['-- ' + x for x in proof.split('\n')])
        return f"**Error**, can not find 'theorem' and ':=' in {error_app}"
    return stats_re[:stats_span_[1]].replace("sorry", "") + proof_str[span[1]:]

# ----------------------------
# Handlers
# ----------------------------

class InferenceHandler:
    def __init__(self):
        pass

    def extrac_code(self, inputs):
        pattern = r'```lean4\n(.*?)\n```'
        matches = re.findall(pattern, inputs, re.DOTALL)
        if matches:
            return matches[-1]
        pattern = r'```lean4\n(.*?)```'
        matches = re.findall(pattern, inputs, re.DOTALL)
        if matches:
            return matches[-1]
        pattern = r'```lean\n(.*?)```'
        matches = re.findall(pattern, inputs, re.DOTALL)
        if matches:
            return matches[-1]
        return "None"

    def clean_code_string(self, code_string):
        lines = code_string.splitlines()
        filtered_lines = [
            line for line in lines
            if not (line.startswith("import") or line.startswith("set_option") or line.startswith("open") or line.strip() == "")
        ]
        return "\n".join(filtered_lines)

    def prover_inference(self, lean4_code, tokenizer):
        raise NotImplementedError

    def generate_correction_prompt(self, lean4_code_original_stmt,
                                   history_messages_from_prev_round,
                                   prev_round_llm_raw_output,
                                   error_message_for_prev_round,
                                   tokenizer, current_correction_round_num,
                                   unsolved_goals_restart_hint: bool = False):
        # Returns (prompt_str, messages_list_for_this_prompt)
        raise NotImplementedError

    def split_list_into_chunks(self, input_list, num_chunks):
        input_list = list(input_list)
        list_length = len(input_list)
        base_chunk_size = list_length // num_chunks
        remainder = list_length % num_chunks

        chunks = []
        index = 0
        for i in range(num_chunks):
            current_chunk_size = base_chunk_size + (1 if i < remainder else 0)
            if index >= list_length or current_chunk_size == 0:
                break
            chunks.append(input_list[index:index + current_chunk_size])
            index += current_chunk_size

        return chunks

    def load_split(self, input_file, split):
        df = pd.read_json(input_file, lines=True)
        if split == "none":
            return df.to_dict(orient='records')
        else:
            return df[df.split.apply(lambda x: str(x) == str(split))].to_dict(orient='records')

    def problem_check(self, statement, full_code):
        return full_code


class DeepSeekCoTHandler(InferenceHandler):
    def __init__(self):
        pass

    def extrac_code(self, inputs):
        import_head = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"
        pattern = r'```lean4\n(.*?)\n```'
        matches = re.findall(pattern, inputs, re.DOTALL)
        if matches:
            return import_head + matches[-1]
        pattern = r'```lean4\n(.*?)```'
        matches = re.findall(pattern, inputs, re.DOTALL)
        if matches:
            return import_head + matches[-1]
        pattern = r'```lean\n(.*?)```'
        matches = re.findall(pattern, inputs, re.DOTALL)
        if matches:
            return import_head + matches[-1]
        return "None"

    def prover_inference(self, lean4_code, tokenizer):
        formal_statement = replace_final_by_suffix(lean4_code, ":= by sorry")
        prompt = (
            f"Complete the following Lean 4 code:\n\n```lean4\n{formal_statement}```\n\n"
            "Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan "
            "outlining the main proof steps and strategies.\nThe plan should highlight key ideas, intermediate lemmas, "
            "and proof structures that will guide the construction of the final formal proof."
        )
        messages = [{"role": "user", "content": prompt}]
        text = tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=True)
        return text, messages

    def problem_check(self, statement, full_code):
        full_code = replace_statement_in_proof(statement, full_code)
        return full_code

    def generate_correction_prompt(self, lean4_code_original_stmt,
                                   history_messages_from_prev_round,
                                   prev_round_llm_raw_output,
                                   error_message_for_prev_round,
                                   tokenizer, current_correction_round_num,
                                   unsolved_goals_restart_hint: bool = False):
        # Re-state the theorem succinctly and build a compact, single-turn prompt
        original_stmt_for_prompt = replace_final_by_suffix(lean4_code_original_stmt, ":= by sorry")

        prev_code_only = compact_previous_code(self.extrac_code(prev_round_llm_raw_output))
        error_message_for_prev_round = compact_correction_feedback(error_message_for_prev_round)

        hint = ""
        if unsolved_goals_restart_hint:
            hint = "\n**Note:** The last two attempts ended with *unsolved goals*. Start a fresh approach and try a different proof strategy.\n"

        user_content = (
            "You previously attempted to prove the following Lean 4 theorem.\n\n"
            f"**Theorem (re-state):**\n```lean4\n{original_stmt_for_prompt}\n```\n"
            f"{hint}"
            f"\nDiagnostic feedback from the compiler:\n{error_message_for_prev_round}\n"
        )
        if prev_code_only != "None":
            user_content += (
                "\n**Previous attempt (Lean block only, for reference):**\n"
                f"```lean4\n{prev_code_only}\n```\n"
            )

        user_content += (
            "\n**Your tasks:**\n"
            "1) Briefly diagnose the failure.\n"
            "2) Produce a fresh, *complete* Lean 4 proof with **no `sorry`**.\n"
            "3) Return exactly one code block: ```lean4 ...``` containing the theorem header and finished proof."
        )

        messages = [{"role": "user", "content": user_content}]
        prompt_str = tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=True)
        return prompt_str, messages


class DeepSeekNonCoTHandler(InferenceHandler):
    def __init__(self):
        pass

    def prover_inference(self, lean4_code, tokenizer):
        formal_statement = replace_final_by_suffix(lean4_code, ":= by")  # completion-style
        prompt = f"Complete the following Lean 4 code:\n\n```lean4\n{formal_statement}"
        return prompt, None

    def generate_correction_prompt(self, lean4_code_original_stmt,
                                   history_messages_from_prev_round,  # Not used
                                   prev_round_llm_raw_output,         # Not used directly
                                   error_message_for_prev_round,
                                   tokenizer, current_correction_round_num,
                                   unsolved_goals_restart_hint: bool = False):
        original_stmt_for_completion = replace_final_by_suffix(lean4_code_original_stmt, ":= by")

        note = ""
        if unsolved_goals_restart_hint:
            note = "-- NOTE: The last two attempts ended with unsolved goals. Restart with a fresh proof strategy.\n"

        error_message_for_prev_round = compact_correction_feedback(error_message_for_prev_round)
        commented_errors = '\n'.join(
            [f'-- {line}' for line in error_message_for_prev_round.splitlines() if line.strip()]
        )

        prompt_str = (
            f"-- Re-prove the theorem below; the previous attempt (Round {current_correction_round_num - 1}) failed.\n"
            f"{note}"
            f"{commented_errors}\n"
            f"-- Requirements: no `sorry`; produce a complete proof.\n\n"
            f"```lean4\n{original_stmt_for_completion}"
        )
        return prompt_str, None  # Non-chat


class KiminaCoTHandler(InferenceHandler):
    def __init__(self):
        pass

    def prover_inference(self, lean4_code, tokenizer):
        formal_statement = replace_final_by_suffix(lean4_code, ":= by")  # Kimina expects no 'sorry'
        problem = self.clean_code_string(formal_statement)
        prompt = "Think about and solve the following problem step by step in Lean 4."
        prompt += f"\n# Problem:{problem}"
        prompt += f"\n# Formal statement:\n```lean4\n{formal_statement}\n```\n"

        messages = [
            {"role": "system", "content": "You are an expert in mathematics and Lean 4."},
            {"role": "user", "content": prompt}
        ]

        text = tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=True)
        return text, messages

    def generate_correction_prompt(self, lean4_code_original_stmt,
                                   history_messages_from_prev_round,
                                   prev_round_llm_raw_output,
                                   error_message_for_prev_round,
                                   tokenizer, current_correction_round_num,
                                   unsolved_goals_restart_hint: bool = False):
        original_stmt_for_completion = replace_final_by_suffix(lean4_code_original_stmt, ":= by")
        prev_code_only = compact_previous_code(self.extrac_code(prev_round_llm_raw_output))
        error_message_for_prev_round = compact_correction_feedback(error_message_for_prev_round)

        hint = ""
        if unsolved_goals_restart_hint:
            hint = "\n**Note:** The last two attempts ended with *unsolved goals*. Start a fresh approach and try a different proof strategy.\n"

        user_content = (
            "Please analyze and correct the following Lean 4 theorem proof.\n\n"
            f"**Theorem (re-state):**\n```lean4\n{original_stmt_for_completion}\n```\n"
            f"{hint}"
            f"Diagnostic feedback:\n{error_message_for_prev_round}\n"
        )
        if prev_code_only != "None":
            user_content += (
                "\n**Previous attempt (Lean block only):**\n"
                f"```lean4\n{prev_code_only}\n```\n"
            )
        user_content += (
            "\n**Please**: (1) briefly diagnose the error, then (2) return exactly one ```lean4``` block "
            "with a complete proof (no `sorry`)."
        )

        messages = [{"role": "user", "content": user_content}]
        prompt_str = tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=True)
        return prompt_str, messages

    def problem_check(self, statement, full_code):
        full_code = replace_statement_in_proof(statement, full_code)
        return full_code


if __name__ == "__main__":
    pass
