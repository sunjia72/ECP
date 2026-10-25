#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Extract ground-truth answer constants and simple admissible vocabularies.

For each formalized entry this script sets
formal_answer_info.used_constants_in_ground_truth.
For MathArena-style names it also adds a coarse admissibility level:

    AIME        -> "basic": numerals only
    APEX/HMMT   -> "arithmetic": numerals, arithmetic, radicals, pi/e
    Putnam      -> "advanced_arithmetic": arithmetic plus common advanced
                   numeric operations

Set, complex-number, polynomial, and tuple constants are controlled by separate
answer-type switches, not by arithmetic levels themselves. Set answers are
split into extensional/intensional modes by answer type and explicit overrides.
Prop-valued answers additionally allow True/False. Predicate and set answers
start from logical/set structure plus elementary arithmetic operations plus a
small curated numeric vocabulary for common set/relation answer expressions.
Ground-truth constants are extracted for validation only; they are not used to
expand the admissible vocabulary or structural admissibility options.
"""

import argparse
import json
import re
import sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

from tqdm import tqdm

PROJECT_ROOT = Path(__file__).resolve().parents[2]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from src.ecp.utils import normalize_sorry_block, run_lean_code

MAX_LEAN_WORKERS = 64
QUANTIFIER_OPTION_KEY = "allow_quantifier"
DATASET_DIR = Path("data/dataset")

DERIVED_FIELD_ORDER = [
    "header",
    "answer_part",
    "answer_part_without_answer",
    "additional_info_after_answer",
    "theorem_part",
    "answer_name",
    "answer_type",
    "formal_answer",
    "formal_answer_info",
    "theorem_part_full",
]

DOC_COMMENT_RE = re.compile(r"/--[\s\S]*?-/", re.MULTILINE)
BLOCK_COMMENT_RE = re.compile(r"/-[\s\S]*?-/", re.MULTILINE)
CONSTANT_RE = re.compile(r"``([A-Za-z0-9_'.]+)")

PRINT_FOL_OPTIONS = "\n".join(
    [
        "set_option pp.piBinderNames.hygienic false",
        "set_option pp.notation true",
        "set_option pp.unicode true",
        "set_option pp.piBinderTypes true",
        "set_option pp.funBinderTypes true",
        "set_option pp.foralls true",
        "set_option pp.numericTypes true",
        "set_option pp.coercions true",
        "set_option pp.coercions.types true",
        "set_option linter.unusedTactic false",
    ]
)

def _tokens(text: str) -> Set[str]:
    return set(text.split())


BASIC_ADMISSIBLE_VOCABULARY: Set[str] = _tokens("OfNat.ofNat")

ARITHMETIC_ADMISSIBLE_VOCABULARY: Set[str] = _tokens("""
    HAdd.hAdd HDiv.hDiv HMul.hMul HPow.hPow HSub.hSub Int.cast Nat.cast Neg.neg
    OfNat.ofNat Rat.cast Real.exp Real.pi Real.sqrt
""")

ELEMENTARY_OPERATION_ADMISSIBLE_VOCABULARY: Set[str] = _tokens("""
    Fin.val HAdd.hAdd HDiv.hDiv HMod.hMod HMul.hMul HPow.hPow HSMul.hSMul
    HSub.hSub Int.cast Nat.cast Nat.digits Nat.factorial Neg.neg OfNat.ofNat
    Rat.cast Real.exp Real.log Real.sin Real.sinh Real.sqrt Subtype.val abs ite
    multiplicity
""")

ADVANCED_NUMERIC_ADMISSIBLE_VOCABULARY: Set[str] = ARITHMETIC_ADMISSIBLE_VOCABULARY | _tokens("""
    Fin.val HMod.hMod HSMul.hSMul Int.ceil Int.ediv Int.emod Int.floor Int.sqrt
    Int.toNat Nat.ceil Nat.choose Nat.digits Nat.factorial Nat.fib Nat.floor
    Nat.gcd Nat.lcm Nat.mod Nat.sqrt Rat.sqrt Real.arccos Real.arcsin Real.arctan
    Real.cos Real.cosh Real.log Real.sin Real.sinh Real.tan Real.tanh Subtype.val
    abs multiplicity
""")

PREDICATE_ADMISSIBLE_VOCABULARY: Set[str] = _tokens("""
    And Dvd.dvd Eq Even False GE.ge GT.gt Iff Int.ModEq LE.le LT.lt
    Membership.mem Nat.ModEq Nat.Prime Ne Not Odd Or Prime True ite
""")

EXTENSIONAL_SET_ADMISSIBLE_VOCABULARY: Set[str] = _tokens("""
    EmptyCollection.emptyCollection Finset.Icc Finset.Ici Finset.Ico Finset.Iic
    Finset.Iio Finset.Ioc Finset.Ioi Finset.Ioo Finset.card Finset.product
    Finset.range Insert.insert Inter.inter Multiset.replicate Set.Icc Set.Ici
    Set.Ico Set.Iic Set.Iio Set.Ioc Set.Ioi Set.Ioo Set.insert Set.singleton
    Set.univ Singleton.singleton Union.union
""")

INTENSIONAL_SET_ADMISSIBLE_VOCABULARY: Set[str] = EXTENSIONAL_SET_ADMISSIBLE_VOCABULARY | _tokens(
    "Membership.mem Set.EqOn Set.Mem Set.image setOf"
)

QUANTIFIER_ADMISSIBLE_VOCABULARY: Set[str] = _tokens("Exists")

COMPLEX_ADMISSIBLE_VOCABULARY: Set[str] = _tokens("Complex.I Complex.mk Complex.ofReal")
POLYNOMIAL_ADMISSIBLE_VOCABULARY: Set[str] = _tokens("""
    MvPolynomial.C MvPolynomial.X Polynomial.C Polynomial.X Polynomial.coeff
    Polynomial.degree Polynomial.eval Polynomial.map Polynomial.natDegree RatFunc.X
""")
TUPLE_ADMISSIBLE_VOCABULARY: Set[str] = _tokens("""
    Fin.val List.cons List.nil Prod.fst Prod.mk Prod.snd Subtype.mk Subtype.val
""")

PROP_ONLY_ADMISSIBLE_VOCABULARY = "[``False, ``True]"

# Problems that require manual inspection (including overlapped problems)
OTHERS_PROBLEM_NAMES: Set[str] = _tokens("putnam_1962_a2 putnam_1974_b1 putnam_1996_a2 putnam_1996_a6 putnam_2018_b1")
SUM_PRODUCT_PROBLEM_NAMES: Set[str] = _tokens("putnam_1975_a4 putnam_1986_a6 putnam_1989_b3")
STRUCTURAL_QUANTIFIER_PROBLEM_NAMES: Set[str] = _tokens("""
    putnam_1962_a2 putnam_1963_b3 putnam_1969_a1 putnam_1972_a3 putnam_1974_b1
    putnam_1979_a3 putnam_1991_a3 putnam_1991_b1 putnam_1996_a6 putnam_2001_a3
    putnam_2005_b2 putnam_2005_b3 putnam_2007_a4 putnam_2008_b5 putnam_2009_b3
    putnam_2010_a2 putnam_2014_b1 putnam_2015_b3 putnam_2016_b5 putnam_2018_b1
    putnam_2021_a3 putnam_2022_b6 putnam_2024_a2 putnam_2024_b1 putnam_2025_a5
""")
INTENSIONAL_SET_PROBLEM_NAMES: Set[str] = _tokens("""
    putnam_1997_b3 putnam_1998_a4 putnam_2011_a4 putnam_2014_b1 putnam_2021_a3
    putnam_2021_a5 putnam_2022_b4 putnam_2023_a6 putnam_2023_b5 putnam_1980_b1
    putnam_1980_b3 putnam_1987_a6 putnam_1988_a3 putnam_1994_b2 putnam_1995_a2
    putnam_2022_a1 putnam_1998_b4 putnam_2012_a5 putnam_2024_b1 putnam_1996_a6
""")

EXTENSIONAL_SET_ANSWER_TYPE_RE = re.compile(
    r"^(?:Set (?:[ℕℝ]|\(ℝ × ℝ\)|\(ℤ × ℤ\))$|Set \(ℕ × ℕ|[ℕℝℤ]\s*→\s*Set\b)"
    r"|\b(?:Finset|List|Multiset)\b|ℂ"
)

OTHERS_ADMISSIBLE_VOCABULARY: Set[str] = _tokens("""
    ContinuousOn Dist.dist Matrix.vecCons Matrix.vecEmpty MeasureTheory.Measure.restrict
    MeasureTheory.MeasureSpace.volume MeasureTheory.average midpoint
""")
SUM_PRODUCT_ADMISSIBLE_VOCABULARY: Set[str] = _tokens("Finset.Icc Finset.prod Finset.range Finset.sum Finset.univ")

def remove_comments(text: str) -> str:
    text = DOC_COMMENT_RE.sub("", text)
    text = BLOCK_COMMENT_RE.sub("", text)
    return re.sub(r"--[^\n]*", "", text)


def normalize_formalization(text: str) -> str:
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    text = re.sub(r"\n{2,}", "\n", text)
    return text.strip("\n")


def starts_with_any(line: str, prefixes: List[str]) -> bool:
    stripped = line.lstrip()
    return any(stripped.startswith(p) for p in prefixes)


def split_formalization(entry: Dict[str, Any]) -> None:
    if entry.get("is_formalized") != "True":
        return

    formalization = entry.get("formalization", "") or ""
    if not formalization.strip():
        return

    lines = normalize_formalization(remove_comments(formalization)).split("\n")
    answer_prefixes = ["noncomputable abbrev ", "abbrev "]

    answer_start: Optional[int] = None
    for i, line in enumerate(lines):
        if starts_with_any(line, answer_prefixes):
            answer_start = i
            break
    if answer_start is None:
        return

    if not entry.get("header"):
        entry["header"] = "\n".join(lines[:answer_start])

    declaration_prefixes = [
        "lemma ",
        "def ",
        "inductive ",
        "variable ",
        "noncomputable def ",
        "noncomputable instance ",
        "namespace ",
        "structure ",
        "constant ",
        "abbrev ",
        "deriving ",
        "mutual ",
        "axiom ",
        "theorem ",
        "open ",
        "example ",
    ]

    answer_end = len(lines)
    for i in range(answer_start + 1, len(lines)):
        if starts_with_any(lines[i], declaration_prefixes):
            answer_end = i
            break

    if not entry.get("answer_part"):
        entry["answer_part"] = normalize_sorry_block("\n".join(lines[answer_start:answer_end]))

    if not entry.get("theorem_part"):
        theorem_start: Optional[int] = None
        for i in range(answer_end, len(lines)):
            if starts_with_any(lines[i], ["theorem "]):
                theorem_start = i
                break
        if theorem_start is not None:
            entry["theorem_part"] = normalize_sorry_block("\n".join(lines[theorem_start:]))
            if not entry.get("additional_info_after_answer"):
                entry["additional_info_after_answer"] = normalize_formalization(
                    "\n".join(lines[answer_end:theorem_start])
                )


def parse_answer_fields(entry: Dict[str, Any]) -> None:
    if entry.get("is_formalized") != "True":
        return

    if not entry.get("answer_part"):
        split_formalization(entry)

    answer_part = normalize_sorry_block(entry.get("answer_part", "") or "")
    if not answer_part.strip():
        return

    m_name = re.search(r"\b(?:noncomputable\s+)?abbrev\s+([^\s:]+)\s*:", answer_part)
    if m_name and not entry.get("answer_name"):
        entry["answer_name"] = m_name.group(1)

    idx_colon = answer_part.find(":")
    idx_assign = answer_part.find(":=", idx_colon + 1) if idx_colon != -1 else -1
    if idx_colon == -1 or idx_assign == -1:
        return

    if not entry.get("answer_type"):
        entry["answer_type"] = answer_part[idx_colon + 1 : idx_assign].strip()
    if not entry.get("formal_answer"):
        entry["formal_answer"] = answer_part[idx_assign + 2 :].strip()
    entry["answer_part_without_answer"] = answer_part[: idx_assign + 2].rstrip() + " sorry"


def process_entry(entry: Dict[str, Any]) -> None:
    split_formalization(entry)
    parse_answer_fields(entry)
    entry.pop("set_type", None)


def extract_backtick_blocks(resp: Any) -> List[str]:
    text = resp if isinstance(resp, str) else json.dumps(resp, ensure_ascii=False)
    return [
        re.sub(r"\s*\n\s*", " ", block.strip().rstrip())
        for block in re.findall(r"```(.*?)```", text, re.DOTALL)
    ]


def response_has_error(resp: Any) -> bool:
    text = resp if isinstance(resp, str) else json.dumps(resp, ensure_ascii=False)
    return "error:" in text


def strip_trailing_sorry(theorem_part: str) -> Optional[str]:
    stripped = theorem_part.rstrip()
    m = re.search(r"\bsorry\s*$", stripped)
    if m is None:
        return None
    return stripped[: m.start()].rstrip()


def build_print_fol_code(entry: Dict[str, Any]) -> Optional[str]:
    theorem_part = normalize_sorry_block(entry.get("theorem_part", "") or "")
    answer_stub = normalize_sorry_block(entry.get("answer_part_without_answer", "") or "")
    if not theorem_part.strip() or not answer_stub.strip():
        return None

    theorem_prefix = strip_trailing_sorry(theorem_part)
    if theorem_prefix is None:
        return None

    pieces = [
        "import utils.fol",
        normalize_formalization(entry.get("header", "") or ""),
        PRINT_FOL_OPTIONS,
        answer_stub,
        normalize_formalization(entry.get("additional_info_after_answer", "") or ""),
        f"{theorem_prefix} print_fol;sorry",
    ]
    return "\n\n".join(piece for piece in pieces if piece.strip()) + "\n"


def extract_fol_formula(entry: Dict[str, Any]) -> Tuple[Optional[str], bool]:
    lean_code = build_print_fol_code(entry)
    if lean_code is None:
        return None, False

    response = run_lean_code(lean_code)
    if response_has_error(response):
        return None, False

    blocks = extract_backtick_blocks(response)
    if not blocks:
        return None, False
    return blocks[0], True


def build_theorem_part_full(entry: Dict[str, Any], fol_formula: str) -> Optional[str]:
    theorem_name = entry.get("name", "") or ""
    answer_name = entry.get("answer_name", "") or ""
    answer_type = entry.get("answer_type", "") or ""
    if not theorem_name or not answer_name or not answer_type or not fol_formula:
        return None
    return f"theorem {theorem_name} : ∃ ({answer_name} : {answer_type}), {fol_formula} := by sorry"


def extract_theorem_part_full(entry: Dict[str, Any]) -> Tuple[Optional[str], bool]:
    fol_formula, success = extract_fol_formula(entry)
    if not success or fol_formula is None:
        return None, False
    theorem_part_full = build_theorem_part_full(entry, fol_formula)
    if theorem_part_full is None:
        return None, False
    return theorem_part_full, True


def parse_used_constants(block: str) -> Set[str]:
    return set(CONSTANT_RE.findall(block or ""))


def format_used_constants(constants: Set[str]) -> str:
    if not constants:
        return "[]"
    return "[" + ", ".join(f"``{name}" for name in sorted(constants)) + "]"


def infer_admissible_level(entry: Dict[str, Any]) -> Optional[str]:
    name = (entry.get("name", "") or "").upper()
    if "AIME" in name:
        return "basic"
    if "APEX" in name or "HMMT" in name:
        return "arithmetic"
    if "PUTNAM" in name:
        return "advanced_arithmetic"
    return None


def answer_type_allows_set(answer_type: str) -> bool:
    return re.search(r"\b(?:Set|Finset|Multiset)\b", answer_type) is not None


def infer_set_type(entry: Dict[str, Any]) -> Optional[str]:
    answer_type = (entry.get("answer_type", "") or "").strip()
    if not answer_type_allows_set(answer_type):
        return None

    name = entry.get("name", "") or ""
    if name in INTENSIONAL_SET_PROBLEM_NAMES:
        return "intensional"
    if EXTENSIONAL_SET_ANSWER_TYPE_RE.search(answer_type):
        return "extensional"
    return "intensional"


def infer_allow_set(entry: Dict[str, Any]) -> str:
    answer_type = entry.get("answer_type", "") or ""
    if not answer_type_allows_set(answer_type):
        return "False"

    return infer_set_type(entry) or "False"


def answer_type_allows_complex(answer_type: str) -> bool:
    return any(token in answer_type for token in ("ℂ", "Complex"))


def answer_type_allows_polynomial(answer_type: str) -> bool:
    return any(token in answer_type for token in ("Polynomial", "MvPolynomial", "RatFunc", "[X]"))


def answer_type_allows_tuple(answer_type: str) -> bool:
    return "×" in answer_type or "Prod" in answer_type


def answer_type_allows_prop(answer_type: str) -> bool:
    return answer_type.strip() == "Prop"


def answer_type_is_relation(answer_type: str) -> bool:
    text = answer_type.replace(" ", "")
    return text.endswith("Prop") and answer_type.strip() != "Prop"


def infer_answer_form(entry: Dict[str, Any]) -> str:
    answer_type = entry.get("answer_type", "") or ""
    name = entry.get("name", "") or ""
    if answer_type_allows_prop(answer_type):
        return "truth_value"
    if name in SUM_PRODUCT_PROBLEM_NAMES:
        return "sum_product_formula"
    if answer_type_allows_set(answer_type):
        allow_set = infer_allow_set(entry)
        return "set_extensional" if allow_set == "extensional" else "set_intensional"
    if answer_type_is_relation(answer_type):
        return "relation_predicate"
    if "→" in answer_type or "->" in answer_type:
        return "function_formula"
    if answer_type_allows_tuple(answer_type):
        return "tuple"
    return "scalar"


def base_numeric_vocabulary(level: Optional[str]) -> Set[str]:
    if level == "basic":
        return set(BASIC_ADMISSIBLE_VOCABULARY)
    if level == "arithmetic":
        return set(ARITHMETIC_ADMISSIBLE_VOCABULARY)
    if level == "advanced_arithmetic":
        return set(ADVANCED_NUMERIC_ADMISSIBLE_VOCABULARY)
    return set()


def build_formal_answer_info(entry: Dict[str, Any], used_constants_for_validation: str) -> Dict[str, str]:
    info = {"used_constants_in_ground_truth": used_constants_for_validation}
    answer_type = entry.get("answer_type", "") or ""
    level = infer_admissible_level(entry)
    answer_form = infer_answer_form(entry)
    allow_prop = answer_type_allows_prop(answer_type)
    if allow_prop:
        info["admissible_vocabulary"] = PROP_ONLY_ADMISSIBLE_VOCABULARY
        if level is not None:
            info["level"] = level
            info["answer_form"] = answer_form
            info["allow_set"] = "False"
            info["allow_complex"] = "False"
            info["allow_polynomial"] = "False"
            info["allow_tuple"] = "False"
            info["allow_prop"] = "True"
            info["others"] = "False"
            info[QUANTIFIER_OPTION_KEY] = "False"
        return info

    if level is not None:
        allow_set = infer_allow_set(entry)
        allow_complex = answer_type_allows_complex(answer_type)
        allow_polynomial = answer_type_allows_polynomial(answer_type)
        allow_tuple = answer_type_allows_tuple(answer_type)
        others = (entry.get("name", "") or "") in OTHERS_PROBLEM_NAMES
        sum_product = (entry.get("name", "") or "") in SUM_PRODUCT_PROBLEM_NAMES
        structural_quantifier = (entry.get("name", "") or "") in STRUCTURAL_QUANTIFIER_PROBLEM_NAMES
        if answer_form in {"relation_predicate", "set_intensional", "set_extensional"}:
            admissible = set(PREDICATE_ADMISSIBLE_VOCABULARY)
            admissible.update(ELEMENTARY_OPERATION_ADMISSIBLE_VOCABULARY)
        else:
            admissible = base_numeric_vocabulary(level)
        if answer_form in {
            "relation_predicate",
            "set_intensional",
            "set_extensional",
            "tuple",
            "function_formula",
            "sum_product_formula",
        }:
            admissible.update(PREDICATE_ADMISSIBLE_VOCABULARY)
        if allow_set == "extensional":
            admissible.update(EXTENSIONAL_SET_ADMISSIBLE_VOCABULARY)
        elif allow_set == "intensional":
            admissible.update(INTENSIONAL_SET_ADMISSIBLE_VOCABULARY)
        if allow_complex:
            admissible.update(COMPLEX_ADMISSIBLE_VOCABULARY)
        if allow_polynomial:
            admissible.update(POLYNOMIAL_ADMISSIBLE_VOCABULARY)
        if allow_tuple:
            admissible.update(TUPLE_ADMISSIBLE_VOCABULARY)
        if others:
            admissible.update(OTHERS_ADMISSIBLE_VOCABULARY)
        if sum_product:
            admissible.update(SUM_PRODUCT_ADMISSIBLE_VOCABULARY)
        if structural_quantifier:
            admissible.update(QUANTIFIER_ADMISSIBLE_VOCABULARY)

        info["level"] = level
        info["answer_form"] = answer_form
        info["allow_set"] = allow_set
        info["allow_complex"] = "True" if allow_complex else "False"
        info["allow_polynomial"] = "True" if allow_polynomial else "False"
        info["allow_tuple"] = "True" if allow_tuple else "False"
        info["allow_prop"] = "True" if allow_prop else "False"
        info["others"] = "True" if others else "False"
        info["sum_product"] = "True" if sum_product else "False"
        info[QUANTIFIER_OPTION_KEY] = "True" if structural_quantifier else "False"
        info["admissible_vocabulary"] = format_used_constants(admissible)
    return info


def extract_answer_constants(header: str, formal_answer: str, answer_type: str) -> Tuple[Set[str], bool]:
    lean_code = (
        "import Mathlib\n"
        "import utils.canonical_all_in_one\n"
        f"{header}\n"
        f"#isCanonical ({formal_answer} : {answer_type}) "
        "with admissible_vocabulary := []\n"
    )
    response = run_lean_code(lean_code)
    blocks = extract_backtick_blocks(response)
    if len(blocks) < 2:
        return set(), False
    return parse_used_constants(blocks[1]), True


def label_used_constants(
    data: List[Dict[str, Any]], max_workers: int, add_theorem_part_full: bool = True
) -> Dict[str, Any]:
    jobs: List[Tuple[int, Dict[str, Any]]] = []
    for idx, entry in enumerate(data):
        if entry.get("is_formalized") == "True":
            process_entry(entry)
            jobs.append((idx, entry))

    def worker(idx: int, entry: Dict[str, Any]) -> Tuple[int, Dict[str, str], bool, Optional[str], bool]:
        formal_answer = entry.get("formal_answer", "") or ""
        answer_type = entry.get("answer_type", "") or ""

        const_success = False
        used_constants = "[]"
        if formal_answer and answer_type:
            try:
                constants, const_success = extract_answer_constants(
                    entry.get("header", "") or "", formal_answer, answer_type
                )
                used_constants = format_used_constants(constants)
            except Exception:
                const_success = False

        theorem_part_full = None
        theorem_success = False
        if add_theorem_part_full:
            try:
                theorem_part_full, theorem_success = extract_theorem_part_full(entry)
            except Exception:
                theorem_part_full = None
                theorem_success = False

        info = build_formal_answer_info(entry, used_constants)
        return idx, info, const_success, theorem_part_full, theorem_success

    ok = 0
    failed = 0
    failed_names: List[str] = []
    theorem_ok = 0
    theorem_failed = 0
    levels: Counter[str] = Counter()
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = [executor.submit(worker, idx, entry) for idx, entry in jobs]
        for fut in tqdm(as_completed(futures), total=len(futures), desc="Processing Lean-derived fields"):
            idx, info, success, theorem_part_full, theorem_success = fut.result()
            data[idx]["formal_answer_info"] = info
            if theorem_part_full is not None:
                data[idx]["theorem_part_full"] = theorem_part_full
            if "level" in info:
                levels[info["level"]] += 1
            if success:
                ok += 1
            else:
                failed += 1
                failed_names.append(str(data[idx].get("name", "")))
            if add_theorem_part_full:
                if theorem_success:
                    theorem_ok += 1
                else:
                    theorem_failed += 1

    return {
        "processed": len(jobs),
        "succeeded": ok,
        "failed": failed,
        "failed_names": failed_names,
        "theorem_part_full_succeeded": theorem_ok,
        "theorem_part_full_failed": theorem_failed,
        "levels": dict(levels),
    }


def validate_admissible_vocabulary_coverage(
    path: Path,
    data: List[Dict[str, Any]],
    extraction_failed_names: Optional[Set[str]] = None,
) -> Dict[str, Any]:
    report_path = path.with_name(f"{path.stem}_admissibility_validation.txt")
    failures = []
    extraction_failures = []
    extraction_failed_names = extraction_failed_names or set()
    checked = 0
    for entry in data:
        if entry.get("is_formalized") != "True":
            continue
        checked += 1
        info = entry.get("formal_answer_info") or {}
        if str(entry.get("name", "")) in extraction_failed_names:
            extraction_failures.append(entry)
            continue
        used_constants = parse_used_constants(info.get("used_constants_in_ground_truth", "[]"))
        admissible = parse_used_constants(info.get("admissible_vocabulary", "[]"))
        missing = used_constants - admissible
        if missing:
            failures.append((entry, missing))

    lines = [
        "# Admissibility Coverage Validation",
        f"dataset: {path}",
        f"checked_formalized_entries: {checked}",
        f"constant_extraction_failures: {len(extraction_failures)}",
        f"constant_coverage_failures: {len(failures)}",
        "",
    ]
    if extraction_failures:
        lines.append("Extraction failures:")
        for entry in extraction_failures:
            lines.extend(
                [
                    f"- name: {entry.get('name', '')}",
                    f"  answer_type: {entry.get('answer_type', '')}",
                    "",
                ]
            )
    if failures:
        lines.append("Failures:")
        for entry, missing in failures:
            info = entry.get("formal_answer_info") or {}
            lines.extend(
                [
                    f"- name: {entry.get('name', '')}",
                    f"  answer_type: {entry.get('answer_type', '')}",
                    f"  answer_form: {info.get('answer_form', '')}",
                    f"  missing_constants: {format_used_constants(missing)}",
                    "",
                ]
            )
    if not extraction_failures and not failures:
        lines.append("All formalized entries have admissible_vocabulary covering used_constants_in_ground_truth.")

    report_path.write_text("\n".join(lines), encoding="utf-8")
    return {
        "checked": checked,
        "constant_extraction_failures": len(extraction_failures),
        "constant_coverage_failures": len(failures),
        "report_path": str(report_path),
    }


def order_processed_entries(data: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    derived_fields = set(DERIVED_FIELD_ORDER)
    ordered_data = []
    for entry in data:
        ordered_entry: Dict[str, Any] = {}
        for key, value in entry.items():
            if key not in derived_fields:
                ordered_entry[key] = value
        for key in DERIVED_FIELD_ORDER:
            if key in entry:
                ordered_entry[key] = entry[key]
        ordered_data.append(ordered_entry)
    return ordered_data


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Label answer constants and admissible vocabularies")
    parser.add_argument("--data_name", type=str, default="matharena", help="Dataset name under data/dataset")
    parser.add_argument(
        "--input_path",
        type=Path,
        default=None,
        help="Input JSON path. Defaults to data/dataset/{data_name}_raw.json",
    )
    parser.add_argument(
        "--output_path",
        type=Path,
        default=None,
        help="Output JSON path. Defaults to data/dataset/{data_name}.json",
    )
    parser.add_argument("--workers", type=int, default=MAX_LEAN_WORKERS, help="Parallel Lean workers")
    parser.add_argument(
        "--skip_theorem_part_full",
        action="store_true",
        help="Do not generate theorem_part_full with utils.fol.print_fol",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    input_path = args.input_path or DATASET_DIR / f"{args.data_name}_raw.json"
    output_path = args.output_path or DATASET_DIR / f"{args.data_name}.json"

    with input_path.open("r", encoding="utf-8") as f:
        data = json.load(f)

    summary = label_used_constants(
        data,
        max_workers=max(1, args.workers),
        add_theorem_part_full=not args.skip_theorem_part_full,
    )
    data = order_processed_entries(data)
    validation = validate_admissible_vocabulary_coverage(output_path, data, set(summary["failed_names"]))
    if validation["constant_extraction_failures"] or validation["constant_coverage_failures"]:
        raise RuntimeError(
            "Admissibility validation failed: "
            f"{validation['constant_extraction_failures']} extraction failures, "
            f"{validation['constant_coverage_failures']} formalized entries have missing constants. "
            f"See {validation['report_path']}"
        )

    with output_path.open("w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)

    print(
        f"Processed {summary['processed']} formalized entries; "
        f"{summary['succeeded']} succeeded, {summary['failed']} failed. "
        f"theorem_part_full: {summary['theorem_part_full_succeeded']} succeeded, "
        f"{summary['theorem_part_full_failed']} failed. "
        f"Levels: {summary['levels']}. "
        f"Validation checked {validation['checked']} entries with "
        f"{validation['constant_extraction_failures']} extraction failures and "
        f"{validation['constant_coverage_failures']} coverage failures. "
        f"Input read from: {input_path}. "
        f"Output written to: {output_path}"
    )


if __name__ == "__main__":
    main()
