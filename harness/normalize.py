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
    """Canonicalize binder blocks: '∀ a b : T, P' → '∀ (a b : T), P'
    
    Handles both '∀ a : T, P' and '∀a : T, P' (with or without space after quantifier).
    Also handles '∀ (a : T), P' which is already in canonical form.
    """
    def repl(m):
        quant = m.group(1)
        # Check if already has parentheses
        if m.group(2).strip().startswith('('):
            return m.group(0)  # Already canonical
        vars_ = re.sub(r"\s+", " ", m.group(2).strip())
        typ   = re.sub(r"\s+", " ", m.group(3).strip())
        rest  = m.group(4) if m.lastindex >= 4 else ""
        return f"{quant} ({vars_} : {typ}), {rest}"
    # Match: quantifier (optional space) vars : type , rest
    # Also handle already parenthesized: quantifier (vars : type), rest
    pattern = r"(∀|∃)\s*((?:\([^)]+\))|(?:[A-Za-z_][A-Za-z_0-9']*(?:\s+[A-Za-z_][A-Za-z_0-9']*)*))\s*:\s*([^,]+),\s*(.*)"
    return re.sub(pattern, repl, s)

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
    """
    S1 normalization: Notation-level equalities that are definitionally equivalent.
    
    Rules (see bank/s1_rules.md):
    1. x ≠ y → ¬ (x = y)  (definitional: ≠ is notation for ¬ (=))
    2. a ≥ b → b ≤ a      (definitional: ≥ is notation for flipped ≤)
    
    Applied to both canonical and candidate for conservative equivalence checking.
    """
    # Rule 2: a ≥ b → b ≤ a (apply before Rule 1 to avoid conflicts)
    def repl_ge(m):
        left = m.group(1).strip()
        right = m.group(2).strip()
        return f"{right} ≤ {left}"
    # Match expressions separated by ≥, avoiding over-matching
    s = re.sub(
        r"([A-Za-z_ℕℤ0-9][A-Za-z_ℕℤ0-9'+\-*/ ]*(?:\([^)]*\))?)\s*≥\s*([A-Za-z_ℕℤ0-9][A-Za-z_ℕℤ0-9'+\-*/ ]*(?:\([^)]*\))?)",
        repl_ge,
        s
    )
    
    # Rule 1: x ≠ y → ¬ (x = y)
    def repl_neq(m):
        left = m.group(1).strip()
        right = m.group(2).strip()
        return f"¬ ({left} = {right})"
    # Match expressions separated by ≠, but not if already in form ¬ (x = y)
    s = re.sub(
        r"([A-Za-z_ℕℤ0-9][A-Za-z_ℕℤ0-9'+\-*/ ]*(?:\([^)]*\))?)\s*≠\s*([A-Za-z_ℕℤ0-9][A-Za-z_ℕℤ0-9'+\-*/ ]*(?:\([^)]*\))?)",
        repl_neq,
        s
    )
    
    # Re-normalize spacing after all rewrites
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
