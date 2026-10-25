# src/goedel/metrics_utils.py
from __future__ import annotations
from typing import Any, Dict

def is_correct_row(compilation_result: Dict[str, Any], code: str, field: str = "complete") -> bool:
    """
    Must match summarize.py's definition exactly.
    """
    ok = bool(compilation_result.get(field, False))
    if not ok:
        return False
    if code is None:
        return False
    # Keep your existing filters:
    if "apply?" in code or "exact?" in code:
        return False
    return True
