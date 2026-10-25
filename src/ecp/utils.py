import os
import re
import subprocess
import json
import textwrap
from pathlib import Path

from typing import List, Tuple, Dict, Any


SET_OPTION_HEADER="\nset_option pp.piBinderNames.hygienic false\nset_option pp.numericTypes true\nset_option pp.coercions true\nset_option pp.coercions.types true\nset_option pp.unicode true\nset_option pp.notation true\nset_option pp.piBinderTypes true\nset_option pp.funBinderTypes true\nset_option pp.foralls true\n"
LEAN_PROJECT_ROOT = Path('Formalization')
DEFAULT_LEAN_TIMEOUT_SECONDS = int(os.environ.get("ECP_LEAN_TIMEOUT_SECONDS", "600"))


def _lean_error_result(message: str) -> Dict[str, Any]:
    return {
        "messages": [
            {
                "severity": "error",
                "data": message,
            }
        ],
        "env": 0,
    }


def run_lean_file(lean_file_path: str) -> Dict[str, Any]:
    """
    Run Lean REPL on a given Lean file using:
        echo '{"path": "...", "allTactics": true}' | lake exe repl

    Returns:
        Parsed JSON dict from the REPL.
    """
    lean_file_path = str(Path(lean_file_path).resolve())
    project_root = LEAN_PROJECT_ROOT

    if not Path(lean_file_path).exists():
        raise FileNotFoundError(f"Lean file not found: {lean_file_path}")
    if not project_root.exists():
        raise FileNotFoundError(f"Project root not found: {project_root}")

    payload = lean_file_path


    try:
        result = subprocess.run(
            ["lake", "env", 'lean', payload],
            cwd=project_root,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=DEFAULT_LEAN_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as exc:
        return (
            "error: Lean execution timed out after "
            f"{DEFAULT_LEAN_TIMEOUT_SECONDS}s.\nSTDOUT:\n{exc.stdout or ''}\nSTDERR:\n{exc.stderr or ''}"
        )

    # stdout, stderr = process.communicate(input=payload)
    if result.stdout:
        msg = result.stdout
    else:
        msg = result.stderr
    # REPL prints JSON; parse it into a dict
    return msg


def run_lean_file_repl(lean_file_path: str) -> Dict[str, Any]:
    """
    Run Lean REPL on a given Lean file using:
        echo '{"path": "...", "allTactics": true}' | lake exe repl

    Returns:
        Parsed JSON dict from the REPL.
    """
    lean_file_path = str(Path(lean_file_path).resolve())
    project_root = LEAN_PROJECT_ROOT

    if not Path(lean_file_path).exists():
        raise FileNotFoundError(f"Lean file not found: {lean_file_path}")
    if not project_root.exists():
        raise FileNotFoundError(f"Project root not found: {project_root}")

    payload = json.dumps({"path": lean_file_path, "allTactics": True})


    repl_dir = os.environ.get('REPL_DIR') if 'REPL_DIR' in os.environ else 'repl'
    process = subprocess.Popen(
        ["lake", "env", repl_dir],
        cwd=project_root,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    try:
        stdout, stderr = process.communicate(
            input=payload,
            timeout=DEFAULT_LEAN_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired:
        process.kill()
        stdout, stderr = process.communicate()
        return _lean_error_result(
            "Lean REPL execution timed out after "
            f"{DEFAULT_LEAN_TIMEOUT_SECONDS}s.\nSTDOUT:\n{stdout}\nSTDERR:\n{stderr}"
        )

    if process.returncode != 0:
        text = (stdout or "").strip()
        if text:
            try:
                return json.loads(text)
            except json.JSONDecodeError:
                pass
        return _lean_error_result(
            f"Lean REPL execution failed with exit code {process.returncode}.\n"
            f"STDOUT:\n{stdout}\nSTDERR:\n{stderr}"
        )

    # REPL prints JSON; parse it into a dict
    try:
        return json.loads(stdout.strip())
    except json.JSONDecodeError as exc:
        return _lean_error_result(
            f"Lean REPL returned invalid JSON: {exc}.\nSTDOUT:\n{stdout}\nSTDERR:\n{stderr}"
        )

def run_lean_code_repl(lean_source: str) -> Dict[str, Any]:
    """
    Create a temporary Lean file in `<project_root>/temp/{random_name}.lean`,
    write `lean_source` into it, run Lean REPL on it, and return parsed JSON.
    """

    from uuid import uuid4  # local import to avoid cycles
    project_root_path = LEAN_PROJECT_ROOT
    if not project_root_path.exists():
        raise FileNotFoundError(f"Project root not found: {project_root_path}")

    temp_dir = project_root_path / "temp"
    temp_dir.mkdir(parents=True, exist_ok=True)

    random_name = f"tmp_{uuid4().hex}_{uuid4().hex}.lean"
    temp_file_path = temp_dir / random_name

    try:
        temp_file_path.write_text(lean_source, encoding="utf-8")
        result = run_lean_file_repl(str(temp_file_path))
    finally:
        try:
            if temp_file_path.exists():
                temp_file_path.unlink()
        except OSError:
            pass

    return result

def verify_answer_syntax(preamble, answer_content, answer_type): 
    repl_result = run_lean_code_repl(
        f'{preamble}\n{SET_OPTION_HEADER}\nnoncomputable def test : {answer_type} := {answer_content}'
    )

    try:
        is_correct = ('messages' not in repl_result) or all(i['severity']!='error' for i in repl_result['messages'])
    except: 
        is_correct = True
    return (is_correct), repl_result


def run_lean_code(lean_source: str) -> Dict[str, Any]:
    """
    Create a temporary Lean file in `<project_root>/temp/{random_name}.lean`,
    write `lean_source` into it, run Lean REPL on it, and return parsed JSON.
    """

    from uuid import uuid4  # local import to avoid cycles
    project_root_path = LEAN_PROJECT_ROOT
    if not project_root_path.exists():
        raise FileNotFoundError(f"Project root not found: {project_root_path}")

    temp_dir = project_root_path / "temp"
    temp_dir.mkdir(parents=True, exist_ok=True)

    random_name = f"tmp_{uuid4().hex}_{uuid4().hex}.lean"
    temp_file_path = temp_dir / random_name

    try:
        temp_file_path.write_text(lean_source, encoding="utf-8")
        result = run_lean_file(str(temp_file_path))
    finally:
        try:
            if temp_file_path.exists():
                temp_file_path.unlink()
        except OSError:
            pass

    return result

def _extract_backtick_blocks_text(resp: Any) -> List[str]:
    s = resp if isinstance(resp, str) else json.dumps(resp, ensure_ascii=False)
    return [b.strip().rstrip().replace("\n", "") for b in re.findall(r"```(.*?)```", s, flags=re.DOTALL)]


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


def canonical_structural_options_suffix(info: Dict[str, Any]) -> str:
    value = _normalize_bool_option(info.get(QUANTIFIER_OPTION_KEY), QUANTIFIER_OPTION_DEFAULT)
    return f"{QUANTIFIER_OPTION_KEY} := {'true' if value else 'false'}"


def verify_answer_admissibility(answer_content, verifier_checker_info):
    header = verifier_checker_info.get("header", "import Mathlib")
    answer_type = verifier_checker_info["answer_type"]
    allowed = (
        verifier_checker_info.get("admissible_vocabulary")
        or "[]"
    )
    structural = canonical_structural_options_suffix(verifier_checker_info)

    lean_code = (
        "import utils.canonical_all_in_one\n"
        f"{header}\n"
        f"{SET_OPTION_HEADER}\n"
        f"#isCanonical ({answer_content}:{answer_type}) with admissible_vocabulary := {allowed} {structural}\n"
    )
    result = run_lean_code(lean_code)
    blocks = _extract_backtick_blocks_text(result)
    first = (blocks[0] if blocks else "").strip()
    if first != "canonical":
        return False
    return True




def parse_lean_in_delimiter(text):
    """Extract the final Lean expression returned by the answer model.

    Tool-using calls can include earlier code snippets in the transcript, so prefer
    the last explicit <<< ... >>> answer delimiter. Fall back to the last Lean code
    fence for compatibility with older prompts.
    """
    if not isinstance(text, str):
        return ""

    matches = re.findall(r"<<<(.*?)>>>", text, re.DOTALL)
    if matches:
        return matches[-1].strip()

    matches = re.findall(r"```lean4?\s*\n*(.*?)```", text, re.DOTALL)
    if matches:
        return matches[-1].strip()

    return ""


def strip_theorem_proof_suffix(s: str) -> str:
    """Return the theorem declaration before its trailing `:= by ...` proof."""
    text = (s or "").strip()
    text = re.sub(r":=\s*by\s*sorry\s*$", "", text, flags=re.DOTALL)
    text = re.sub(r":=\s*by\s*$", "", text, flags=re.DOTALL)
    return text.strip()

def normalize_sorry_block(text: str) -> str:
    """Normalize variants like ':=\n by sorry', ':= by \n sorry', etc., to ':= by sorry'."""
    if not text:
        return text
    return re.sub(r":=\s*by\s*sorry", ":= by sorry", text)

def substitute_answer(formal_answer, answer_name ,answer_type, theorem_part):
    

    replacement = f"({formal_answer} : {answer_type})"
    pattern = r"\b" + re.escape(answer_name) + r"\b"
    theorem_part_with_answer = re.sub(pattern, replacement, theorem_part)
    theorem_part_with_answer = normalize_sorry_block(theorem_part_with_answer)
    return theorem_part_with_answer


def _find_balanced_close(text: str, open_idx: int) -> int:
    depth = 0
    pairs = {"(": ")", "[": "]", "{": "}"}
    opens = set(pairs)
    closes = {v: k for k, v in pairs.items()}
    for idx in range(open_idx, len(text)):
        ch = text[idx]
        if ch in opens:
            depth += 1
        elif ch in closes:
            depth -= 1
            if depth == 0:
                return idx
    return -1


def _split_theorem_name_and_prop(theorem_part: str) -> Tuple[str, str]:
    decl = strip_theorem_proof_suffix(theorem_part)
    match = re.match(r"\s*theorem\s+([^\s:]+)\s*:\s*(.*)\s*$", decl, flags=re.DOTALL)
    if not match:
        raise ValueError("Expected theorem_part_full to have shape `theorem name : proposition := by sorry`.")
    return match.group(1), match.group(2).strip()


def extract_outer_exists_binder_from_prop(prop: str) -> Tuple[str, str, str]:
    """Return the outer existential binder name, binder type, and body.

    Expected shape:
        ∃ (answer_name : AnswerType), body
    """
    text = (prop or "").strip()
    if not text.startswith("∃"):
        raise ValueError("Expected theorem_part_full proposition to start with an outer existential quantifier.")

    idx = 1
    while idx < len(text) and text[idx].isspace():
        idx += 1

    if idx < len(text) and text[idx] == "(":
        close_idx = _find_balanced_close(text, idx)
        if close_idx < 0:
            raise ValueError("Could not parse the outer existential binder.")
        binder = text[idx + 1:close_idx].strip()
        rest = text[close_idx + 1:].lstrip()
        if not rest.startswith(","):
            raise ValueError("Expected a comma after the outer existential binder.")
        body = rest[1:].strip()
    else:
        comma_idx = text.find(",", idx)
        if comma_idx < 0:
            raise ValueError("Expected a comma after the outer existential binder.")
        binder = text[idx:comma_idx].strip()
        body = text[comma_idx + 1:].strip()

    if ":" not in binder:
        raise ValueError("Expected the outer existential binder to include an explicit type.")
    binder_names, binder_type = binder.split(":", 1)
    names = binder_names.strip().split()
    if len(names) != 1:
        raise ValueError(
            "Expected exactly one outer existential answer binder, "
            f"but found `{binder_names.strip()}`."
        )
    binder_name = names[0]
    binder_type = binder_type.strip()
    if not binder_type:
        raise ValueError("Expected a nonempty answer type in the outer existential binder.")
    return binder_name, binder_type, body


def extract_outer_exists_binder(theorem_part_full: str) -> Tuple[str, str, str]:
    """Return the outer answer binder from a theorem declaration.

    The return value is `(answer_name, answer_type, body_after_outer_exists)`.
    """
    _, prop = _split_theorem_name_and_prop(theorem_part_full)
    return extract_outer_exists_binder_from_prop(prop)


def _extract_outer_exists_body(prop: str, answer_name: str) -> str:
    binder_name, _, body = extract_outer_exists_binder_from_prop(prop)
    if binder_name != answer_name:
        raise ValueError(
            f"Outer existential binder `{binder_name}` does not match answer_name `{answer_name}`."
        )
    return body


def answer_substituted_theorem(entry: Dict[str, Any], answer_content: str, negated: bool = False) -> str:
    """Build the theorem sent to the prover after eliminating the answer existential.

    Input theorem:
        theorem T : ∃ (ans : A), body ans := by sorry

    Output theorem:
        theorem T_answer_substituted : body (candidate : A) := by

    For refutation runs, output `¬ (body (candidate : A))`.
    """
    name = entry["name"]
    answer_name = entry["answer_name"]
    answer_type = entry["answer_type"]
    theorem_part_full = entry.get("theorem_part_full")
    if not theorem_part_full:
        raise ValueError(f"{name} is missing theorem_part_full.")

    original_theorem_name, prop = _split_theorem_name_and_prop(theorem_part_full)
    body = _extract_outer_exists_body(prop, answer_name=answer_name)
    body = substitute_answer(answer_content, answer_name, answer_type, body)

    theorem_name = _sanitize_lean_ident(
        f"{original_theorem_name}_{'answer_refuted' if negated else 'answer_substituted'}"
    )
    proposition = f"¬ ({body})" if negated else body
    return f"theorem {theorem_name} : {proposition} := by "


def full_problem_statement(entry: Dict[str, Any]) -> str:
    return "\n".join(
        part for part in [
            entry.get("header", ""),
            entry.get("additional_info_after_answer", ""),
            entry.get("theorem_part_full", ""),
        ] if part
    )


def ecp_preamble(entry: Dict[str, Any]) -> str:
    return "\n".join(
        part for part in [
            entry.get("header", ""),
            entry.get("additional_info_after_answer", ""),
        ] if part
    )


def extract_proof_body(lean_code: str) -> str:
    """Extract the proof body after the final theorem's `:= by`."""
    if not isinstance(lean_code, str):
        return ""
    matches = list(re.finditer(r"\btheorem\b.*?:=\s*by\b", lean_code, flags=re.DOTALL))
    if not matches:
        return textwrap.dedent(lean_code).strip()
    return textwrap.dedent(lean_code[matches[-1].end():]).strip()


def indent_lean_block(code: str, spaces: int = 2) -> str:
    prefix = " " * spaces
    lines = textwrap.dedent(code or "").strip().splitlines()
    if not lines:
        return ""
    return "\n".join(prefix + line if line.strip() else "" for line in lines)


def assemble_existential_proof(entry: Dict[str, Any], answer_content: str, proof_body: str) -> str:
    """Assemble a proof for the original theorem_part_full from a substituted proof body."""
    theorem_decl = strip_theorem_proof_suffix(entry["theorem_part_full"])
    answer_type = entry["answer_type"]
    body = indent_lean_block(proof_body, spaces=2)
    if body:
        proof = f"{theorem_decl} := by\n  use ({answer_content} : {answer_type})\n{body}\n"
    else:
        proof = f"{theorem_decl} := by\n  use ({answer_content} : {answer_type})\n"
    return "\n".join(part for part in [ecp_preamble(entry), proof] if part)


def is_true_value(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value.strip().lower() == "true"
    return bool(value)

    
def formal_equivalence_checker(name, header, answer_type, answer_1, answer_2) -> str:
    temp_dir = Path("Formalization/Temp")
    temp_dir.mkdir(parents=True, exist_ok=True)

    # Write with-answer version
    from uuid import uuid4
    filename = temp_dir / f"{name}_{uuid4().hex}.lean"
    proc = None
    try:
        with open(filename, 'w') as f:
            f.write(
                "import utils.fol\n"
                f"{header}\n"
                f"theorem check_equality : ({answer_1} : {answer_type}) = ({answer_2} : {answer_type}) := by \n"
                "try_solvers\n"
            )
        # Run the command in the specified working directory

        project_dir = str(filename).split('/')[0]
        file_dir = '/'.join(str(filename).split('/')[1:])

        proc = subprocess.run(
            ["lake", "env", "lean", file_dir],  # Just check the file
            cwd=project_dir,
            capture_output=True,
            text=True,
        )
    finally:
        try:
            if filename.exists():
                filename.unlink()
            if temp_dir.exists() and not any(temp_dir.iterdir()):
                temp_dir.rmdir()
        except OSError:
            pass

    if proc is None:
        return "False"
    result = f"{proc.stdout}\n{proc.stderr}".strip()
    # match = re.search(r"error: unsolved goals\n(.+)", result, flags=re.DOTALL)
    if proc.returncode == 0 and "error:" not in result and "True" in result:
        return "True"
    return "False"


def auto_set_cuda_visible_devices():
    try:
        # Count the number of GPUs
        output = subprocess.check_output(["nvidia-smi", "-L"], encoding="utf-8")
        num_gpus = output.count("GPU ")
        # Set CUDA_VISIBLE_DEVICES to all GPU indices
        os.environ["CUDA_VISIBLE_DEVICES"] = ",".join(str(i) for i in range(num_gpus))
        print(f"Set CUDA_VISIBLE_DEVICES to: {os.environ['CUDA_VISIBLE_DEVICES']}")
    except Exception as e:
        print(f"Could not set CUDA_VISIBLE_DEVICES automatically: {e}")
        



def _sanitize_lean_ident(name: str) -> str:
    # Lean identifiers cannot contain many punctuation characters.
    # Your dataset names look safe, but make this robust.
    out = []
    for ch in str(name):
        if ch.isalnum() or ch in ["_"]:
            out.append(ch)
        else:
            out.append("_")
    s = "".join(out)
    if not s:
        s = "anon"
    if s[0].isdigit():
        s = f"n_{s}"
    return s
