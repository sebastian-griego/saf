"""
diff_explain.py — structured diffs to make rejections actionable

When S0 strings mismatch, we still want to help a human adjudicator quickly
see *how* they differ. We extract a few lightweight features:

- quantifier profile: sequence of quantifiers and variable types
- operator skeleton: order of logical/relational operators (=, ≤, <, ≠, ↔, →)
- type mentions: ℕ, ℤ, ℚ, ℝ (very coarse)
"""
import re
from typing import Dict

OPS = ["=", "≤", "≥", "<", ">", "≠", "↔", "→"]
TYPES = ["ℕ", "ℤ", "ℚ", "ℝ"]

_q_pat = re.compile(r"(∀|∃)\s*\(([^)]*)\)\s*,")
# fallback for non-parenthesized binders (rare after S0 normalization)
_q_fallback = re.compile(r"(∀|∃)\s+([A-Za-z_][A-Za-z_0-9'\s]*?)\s*:\s*([^,]+),")

def _split_vars(block: str):
    # e.g., "a b : ℕ" or "a : ℕ"
    block = block.strip()
    if ":" not in block:
        return [], None
    vars_part, typ = block.split(":", 1)
    vars_ = [v for v in re.split(r"\s+", vars_part.strip()) if v]
    typ = typ.strip()
    return vars_, typ

def quantifier_profile(s: str):
    prof = []
    for m in _q_pat.finditer(s):
        quant = m.group(1)
        inner = m.group(2)
        vars_, typ = _split_vars(inner)
        prof.append({"quant": quant, "vars": vars_, "type": typ})
    # fallback if no parenthesized binders
    if not prof:
        for m in _q_fallback.finditer(s):
            quant = m.group(1)
            vars_ = [v for v in re.split(r"\s+", m.group(2).strip()) if v]
            typ = m.group(3).strip()
            prof.append({"quant": quant, "vars": vars_, "type": typ})
    return prof

def operator_skeleton(s: str):
    seq = []
    for ch in s:
        if ch in OPS:
            seq.append(ch)
    return "".join(seq)

def type_mentions(s: str):
    present = [t for t in TYPES if t in s]
    return present

def summarize(s: str) -> Dict:
    return {
        "quantifiers": quantifier_profile(s),
        "operators": operator_skeleton(s),
        "types": type_mentions(s),
        "length": len(s)
    }
