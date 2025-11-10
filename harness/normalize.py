"""Normalization for Lean proposition strings: S0 (formatting) and S1 (semantic rewrites)."""
import re

ASCII_TO_UNICODE = [
    (r"<->", "↔"),
    (r"->", "→"),
    (r"!=", "≠"),
    (r"forall", "∀"),
    (r"exists", "∃"),
]

def _collapse_ws(s: str) -> str:
    """Replace runs of whitespace with a single space; strip ends."""
    s = re.sub(r"\s+", " ", s)
    return s.strip()

def _ascii_to_unicode(s: str) -> str:
    """Map common ASCII spellings to Lean's Unicode notations."""
    for a, u in ASCII_TO_UNICODE:
        s = re.sub(a, u, s)
    return s

def _normalize_binders(s: str) -> str:
    """Canonicalize binder blocks: '∀ a b : T, P' → '∀ (a b : T), P'"""
    def repl(m):
        quant = m.group(1)
        vars_ = re.sub(r"\s+", " ", m.group(2).strip())
        typ   = re.sub(r"\s+", " ", m.group(3).strip())
        rest  = m.group(4) if m.lastindex >= 4 else ""
        return f"{quant} ({vars_} : {typ}), {rest}"
    return re.sub(r"(∀|∃)\s+((?:[A-Za-z_][A-Za-z_0-9']*\s*)+)\s*:\s*([^,]+),\s*(.*)", repl, s)

def _punct_space(s: str) -> str:
    """Normalize spaces around punctuation and common operators."""
    s = re.sub(r"\s*,\s*", ", ", s)
    s = re.sub(r"\s*:\s*", " : ", s)
    s = re.sub(r"\(\s*", "(", s)
    s = re.sub(r"\s*\)", ")", s)
    s = re.sub(r"\s*=\s*", " = ", s)
    s = re.sub(r"\s*≤\s*", " ≤ ", s)
    s = re.sub(r"\s*≥\s*", " ≥ ", s)
    s = re.sub(r"\s*↔\s*", " ↔ ", s)
    s = re.sub(r"\s*→\s*", " → ", s)
    s = re.sub(r"\s*≠\s*", " ≠ ", s)
    s = re.sub(r"\s*∧\s*", " ∧ ", s)
    s = re.sub(r"\s*∨\s*", " ∨ ", s)
    return s

def _normalize_s1(s: str) -> str:
    """S1 normalization: semantic rewrites applied to both canonical and candidate."""
    def repl_not_exists(m):
        return f"∀ {m.group(1)}, ¬ {m.group(2)}"
    s = re.sub(r"¬\s*∃\s*(\([^)]+\)),\s*(.+)", repl_not_exists, s)
    
    def repl_ge(m):
        return f"{m.group(2).strip()} ≤ {m.group(1).strip()}"
    s = re.sub(r"([A-Za-z_ℕℤ0-9][A-Za-z_ℕℤ0-9'\+\-*/ ]*(?:\([^)]*\))?)\s*≥\s*([A-Za-z_ℕℤ0-9][A-Za-z_ℕℤ0-9'\+\-*/ ]*(?:\([^)]*\))?)", repl_ge, s)
    
    def repl_neq(m):
        return f"¬ ({m.group(1).strip()} = {m.group(2).strip()})"
    s = re.sub(r"([A-Za-z_ℕℤ0-9][A-Za-z_ℕℤ0-9'\+\-*/ ]*(?:\([^)]*\))?)\s*≠\s*([A-Za-z_ℕℤ0-9][A-Za-z_ℕℤ0-9'\+\-*/ ]*(?:\([^)]*\))?)", repl_neq, s)
    
    s = _punct_space(s)
    return s.strip()

def normalize_lean_prop(s: str, use_s1: bool = False) -> str:
    """Normalization pipeline: S0 (always) + S1 (optional)."""
    s = _collapse_ws(s)
    s = _ascii_to_unicode(s)
    s = _normalize_binders(s)
    s = _punct_space(s)
    s = s.strip()
    
    if use_s1:
        s = _normalize_s1(s)
    
    return s
