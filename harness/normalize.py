"""
normalize.py — deterministic normalization for Lean proposition strings

S0 (always on): Collapse whitespace, ASCII↔Unicode, binder style, operator spacing.
S1 (optional): Small, audited rewrites:
  - x ≠ y → ¬ (x = y)
  - a ≥ b → b ≤ a
  - ¬ ∃ (x : T), P x → ∀ (x : T), ¬ P x
"""
import re

ASCII_TO_UNICODE = [
    (r"<->", "↔"),   # bi-implication
    (r"->", "→"),    # implication
    (r"!=", "≠"),    # not equal
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
    r"""
    Canonicalize binder blocks:
      '∀ a b : T, P' → '∀ (a b : T), P'
      '∃ a b : T, P' → '∃ (a b : T), P'

    Regex groups:
      (1): quantifier '∀' or '∃'
      (2): variable list 'a b c'
      (3): type 'T'
      (4): everything after the comma ', P...'
    """
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
    return s

def _normalize_s1(s: str) -> str:
    """
    S1 normalization: Small, audited semantic rewrites.
    Applied to both canonical and candidate.
    Rules:
    1. x ≠ y → ¬ (x = y)
    2. a ≥ b → b ≤ a
    3. ¬ ∃ (x : T), P x → ∀ (x : T), ¬ P x
    """
    # Rule 3 first (before other transformations): ¬ ∃ (x : T), P → ∀ (x : T), ¬ P
    def repl_not_exists(m):
        binder = m.group(1)  # "(x : T)" 
        rest = m.group(2)    # "P x"
        return f"∀ {binder}, ¬ {rest}"
    s = re.sub(r"¬\s*∃\s*(\([^)]+\)),\s*(.+)", repl_not_exists, s)
    
    # Rule 2: a ≥ b → b ≤ a (flip sides)
    def repl_ge(m):
        left = m.group(1).strip()
        right = m.group(2).strip()
        return f"{right} ≤ {left}"
    # Match expressions separated by ≥, avoiding over-matching
    # Look for word boundaries or operators to delimit expressions
    s = re.sub(r"([A-Za-z_ℕℤ0-9][A-Za-z_ℕℤ0-9'\+\-*/ ]*(?:\([^)]*\))?)\s*≥\s*([A-Za-z_ℕℤ0-9][A-Za-z_ℕℤ0-9'\+\-*/ ]*(?:\([^)]*\))?)", repl_ge, s)
    
    # Rule 1: x ≠ y → ¬ (x = y)
    # Apply after other rules to avoid conflicts
    def repl_neq(m):
        left = m.group(1).strip()
        right = m.group(2).strip()
        return f"¬ ({left} = {right})"
    # Match simple expressions before and after ≠
    # Avoid matching if already in form ¬ (x = y) by checking context
    # But since we're applying to normalized strings, just transform all ≠
    s = re.sub(r"([A-Za-z_ℕℤ0-9][A-Za-z_ℕℤ0-9'\+\-*/ ]*(?:\([^)]*\))?)\s*≠\s*([A-Za-z_ℕℤ0-9][A-Za-z_ℕℤ0-9'\+\-*/ ]*(?:\([^)]*\))?)", repl_neq, s)
    
    # Re-normalize spacing after all rewrites
    s = _punct_space(s)
    return s.strip()

def normalize_lean_prop(s: str, use_s1: bool = False) -> str:
    """
    Normalization pipeline: S0 (always) + S1 (optional).
    
    Args:
        s: Lean proposition string
        use_s1: If True, apply S1 semantic rewrites after S0
    """
    # S0 normalization (always)
    s = _collapse_ws(s)
    s = _ascii_to_unicode(s)
    s = _normalize_binders(s)
    s = _punct_space(s)
    s = s.strip()
    
    # S1 normalization (optional)
    if use_s1:
        s = _normalize_s1(s)
    
    return s
