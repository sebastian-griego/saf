"""Normalization for Lean proposition strings: S0 (formatting) and S1 (semantic rewrites)."""
import re
import unicodedata
from typing import Dict, List, Tuple

# Source of truth for S1 normalization rules
S1_RULES_FILE = "bank/s1_rules.md"

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

def _alpha_rename(s: str) -> str:
    """
    Alpha-renaming: Normalize bound variable names to canonical form.
    
    Renames bound variables in quantifiers (∀, ∃) to canonical names (x₁, x₂, ...)
    based on their position in each scope. This ensures that α-equivalent propositions
    are recognized as equivalent.
    
    Example:
    - Input: ∀ (a : ℕ), ∃ (b : ℕ), a = b
    - Output: ∀ (x₁ : ℕ), ∃ (x₁ : ℕ), x₁ = x₁
    
    Note: Each quantifier scope gets fresh canonical names starting from x₁.
    Variables are renamed within their scope, preserving the binding structure.
    """
    def get_canonical_name(index: int) -> str:
        """Generate canonical variable name: x₁, x₂, x₃, ...
        
        Args:
            index: 0-based index (0 -> x₁, 1 -> x₂, etc.)
        """
        # Unicode subscript digits: ₀₁₂₃₄₅₆₇₈₉
        subscripts = ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉']
        
        # Convert index to 1-based for display (0 -> 1, 1 -> 2, etc.)
        num = index + 1
        
        # Convert number to subscript string
        if num < 10:
            return f"x{subscripts[num]}"
        else:
            # For numbers >= 10, convert each digit to subscript
            digits = []
            while num > 0:
                digits.append(subscripts[num % 10])
                num //= 10
            return "x" + "".join(reversed(digits))
    
    def parse_binder_vars(binder_str: str) -> Tuple[List[str], str]:
        """Extract variable names and type from a binder string.
        
        Returns: (list of variable names, type string)
        """
        binder_str = binder_str.strip()
        if ':' in binder_str:
            vars_part, type_part = binder_str.split(':', 1)
            vars_part = vars_part.strip()
            type_part = type_part.strip()
        else:
            vars_part = binder_str
            type_part = ""
        
        # Split by whitespace to get individual variable names
        vars_list = [v.strip() for v in re.split(r'\s+', vars_part) if v.strip()]
        return vars_list, type_part
    
    def rename_variable_occurrences(text: str, old_name: str, new_name: str) -> str:
        """Replace all occurrences of a variable name, respecting word boundaries."""
        # Match variable name that is:
        # - At start of string or preceded by non-identifier char
        # - Followed by non-identifier char or end of string
        # This avoids matching variable names that are part of larger identifiers
        pattern = r'(^|[^A-Za-z_0-9\'])(' + re.escape(old_name) + r')([^A-Za-z_0-9\']|$)'
        def repl(match):
            return match.group(1) + new_name + match.group(3)
        return re.sub(pattern, repl, text)
    
    def process_expression(text: str) -> str:
        """Process an expression, renaming bound variables in quantifiers.
        
        Processes quantifiers from left to right (outermost first).
        Each quantifier scope gets fresh canonical variable names (x₁, x₂, ...).
        """
        text = text.strip()
        if not text:
            return text
        
        # Pattern to match quantifier at the start: ∀ (binders), or ∃ (binders),
        # Note: [^)]+ will not handle nested parens in types, but S0 normalization
        # should ensure types are simple enough for this to work
        quantifier_pattern = r'^(∀|∃)\s*\(([^)]+)\)\s*,(.*)$'
        
        match = re.match(quantifier_pattern, text)
        if not match:
            # No quantifier at the start, return as-is
            return text
        
        quant = match.group(1)
        binder_content = match.group(2)
        rest = match.group(3).strip()
        
        # Parse binder variables
        var_names, type_str = parse_binder_vars(binder_content)
        if not var_names:
            # No variables to rename, but still process the rest
            processed_rest = process_expression(rest)
            return f"{quant} ({binder_content}), {processed_rest}"
        
        # Generate canonical names for this quantifier's variables
        # Each scope gets fresh names starting from x₁
        renamings = {}
        canonical_vars = []
        for i, var_name in enumerate(var_names):
            canonical_name = get_canonical_name(i)
            renamings[var_name] = canonical_name
            canonical_vars.append(canonical_name)
        
        # Rebuild binder with canonical names
        if type_str:
            new_binder = f"{' '.join(canonical_vars)} : {type_str}"
        else:
            new_binder = ' '.join(canonical_vars)
        
        # First, apply renamings to the body to handle any free occurrences
        # of variables that are about to be bound (shouldn't happen in well-formed prop, but be safe)
        # Actually, we should process nested quantifiers first, then apply renamings
        
        # Process the body recursively (this will handle nested quantifiers)
        processed_body = process_expression(rest)
        
        # Now apply renamings to the processed body
        # This replaces free occurrences of the old variable names with canonical names
        # Sort by length (longest first) to avoid partial matches
        for old_name, new_name in sorted(renamings.items(), key=lambda x: len(x[0]), reverse=True):
            processed_body = rename_variable_occurrences(processed_body, old_name, new_name)
        
        return f"{quant} ({new_binder}), {processed_body}"
    
    return process_expression(s)

def _normalize_s1(s: str) -> str:
    """
    S1 normalization: Notation-level equalities that are definitionally equivalent.
    
    Rules are documented in the source of truth: bank/s1_rules.md
    
    Rules are applied in order:
    0. Alpha-renaming: Normalize bound variable names to canonical form (x₁, x₂, ...)
    1. x ≠ y → ¬ (x = y)  (definitional: ≠ is notation for ¬ (=))
    2. a ≥ b → b ≤ a      (definitional: ≥ is notation for flipped ≤)
    
    Applied to both canonical and candidate for conservative equivalence checking.
    """
    # Rule 0: Alpha-renaming (apply first to normalize variable names)
    s = _alpha_rename(s)
    
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
    s = unicodedata.normalize("NFKC", s)
    s = _ascii_to_unicode(s)
    s = _normalize_binders(s)
    s = _punct_space(s)
    s = s.strip()
    
    if use_s1:
        s = _normalize_s1(s)
    
    return s
