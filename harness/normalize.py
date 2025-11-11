"""Normalization for Lean proposition strings: S0 (formatting) and S1 (semantic rewrites)."""
import re
import unicodedata
from typing import List, Tuple

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
    # Normalize negation: remove space after ¬ (¬ P → ¬P)
    s = re.sub(r"¬\s+", "¬", s)
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
        # Handle both single binder: ∀ (x : T), P
        # and multiple binders: ∀ (x : T) (y : U), P
        # First try to match multiple binders format: (x : T) (y : U), ...
        multi_binder_pattern = r'^(∀|∃)\s*((?:\([^)]+\)\s*)+),\s*(.*)$'
        multi_match = re.match(multi_binder_pattern, text)
        
        if multi_match:
            quant = multi_match.group(1)
            binders_str = multi_match.group(2).strip()
            rest = multi_match.group(3).strip()
            
            # Extract all binders: (x : T), (y : U), etc.
            binder_pattern = r'\(([^)]+)\)'
            all_binders = re.findall(binder_pattern, binders_str)
            
            if all_binders:
                # Collect all variables from all binders
                all_var_names = []
                all_binder_parts = []
                var_index = 0
                renamings = {}
                
                for binder_content in all_binders:
                    var_names, type_str = parse_binder_vars(binder_content)
                    if var_names:
                        canonical_vars = []
                        for var_name in var_names:
                            canonical_name = get_canonical_name(var_index)
                            renamings[var_name] = canonical_name
                            canonical_vars.append(canonical_name)
                            var_index += 1
                        
                        if type_str:
                            new_binder = f"{' '.join(canonical_vars)} : {type_str}"
                        else:
                            new_binder = ' '.join(canonical_vars)
                        all_binder_parts.append(f"({new_binder})")
                    else:
                        all_binder_parts.append(f"({binder_content})")
                
                # Process the body recursively
                processed_body = process_expression(rest)
                
                # Apply renamings to the processed body
                for old_name, new_name in sorted(renamings.items(), key=lambda x: len(x[0]), reverse=True):
                    processed_body = rename_variable_occurrences(processed_body, old_name, new_name)
                
                combined_binders = ' '.join(all_binder_parts)
                return f"{quant} {combined_binders}, {processed_body}"
        
        # Fall back to single binder pattern: ∀ (binders), ...
        quantifier_pattern = r'^(∀|∃)\s*\(([^)]+)\)\s*,\s*(.*)$'
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
        
        # Process the body recursively (this will handle nested quantifiers)
        processed_body = process_expression(rest)
        
        # Now apply renamings to the processed body
        # This replaces free occurrences of the old variable names with canonical names
        # Sort by length (longest first) to avoid partial matches
        for old_name, new_name in sorted(renamings.items(), key=lambda x: len(x[0]), reverse=True):
            processed_body = rename_variable_occurrences(processed_body, old_name, new_name)
        
        return f"{quant} ({new_binder}), {processed_body}"
    
    return process_expression(s)

def _find_matching_paren(s: str, start: int) -> int:
    """Find the matching closing parenthesis for an opening one at position start."""
    depth = 0
    for i in range(start, len(s)):
        if s[i] == '(':
            depth += 1
        elif s[i] == ')':
            depth -= 1
            if depth == 0:
                return i
    return -1

def _split_by_operator(expr: str, op: str) -> List[str]:
    """Split expression by operator at top level (respecting parentheses)."""
    parts = []
    depth = 0
    start = 0
    i = 0
    expr_stripped = expr.strip()
    while i < len(expr_stripped):
        if expr_stripped[i] == '(':
            depth += 1
        elif expr_stripped[i] == ')':
            depth -= 1
        elif depth == 0:
            # Check if we have the operator at this position (with possible leading whitespace)
            # Skip leading whitespace
            j = i
            while j < len(expr_stripped) and expr_stripped[j].isspace():
                j += 1
            # Check if operator starts here
            if j < len(expr_stripped) and expr_stripped[j:j+len(op)] == op:
                # Found operator at top level
                part = expr_stripped[start:i].strip()
                if part:
                    parts.append(part)
                # Skip operator and any trailing whitespace
                i = j + len(op)
                while i < len(expr_stripped) and expr_stripped[i].isspace():
                    i += 1
                start = i
                continue
        i += 1
    
    # Add the last part
    if start < len(expr_stripped):
        part = expr_stripped[start:].strip()
        if part:
            parts.append(part)
    
    return parts if len(parts) >= 2 else [expr]

def _normalize_logical_structure(s: str) -> str:
    """
    Normalize logical structure by applying equivalence rules recursively.
    
    Rules applied (in order):
    1. Double negation elimination: ¬¬P → P
    2. De Morgan's laws: ¬(P ∧ Q) → (¬P ∨ ¬Q), ¬(P ∨ Q) → (¬P ∧ ¬Q)
    3. Quantifier negation: ¬∃ (x : T), P → ∀ (x : T), ¬P, ¬∀ (x : T), P → ∃ (x : T), ¬P
    4. Contrapositive: P → Q → ¬Q → ¬P
    5a. Associativity: Flatten nested ∧ and ∨ structures: (P ∧ Q) ∧ R → P ∧ Q ∧ R
    5b. Commutativity: Normalize order of ∧ and ∨ operands (lexicographic)
    6. Binder normalization: Flatten nested quantifiers of same type: ∀ (x : T), ∀ (y : U), P → ∀ (x : T) (y : U), P
    
    Returns normalized formula string.
    """
    s = s.strip()
    if not s:
        return s
    
    def normalize_rec(expr: str) -> str:
        """Recursively normalize a logical expression."""
        expr = expr.strip()
        if not expr:
            return expr
        
        # Rule 1: Double negation elimination: ¬¬P → P
        double_neg_match = re.match(r'^¬\s*¬\s*(.+)$', expr)
        if double_neg_match:
            inner = double_neg_match.group(1).strip()
            return normalize_rec(inner)
        
        # Rule 2: De Morgan's laws - handle negated conjunctions/disjunctions
        # First check if we have ¬( ... )
        if expr.startswith('¬') and expr[1:].strip().startswith('('):
            # Find the matching closing paren
            inner_start = expr.find('(')
            close_paren = _find_matching_paren(expr, inner_start)
            if close_paren > 0:
                inner = expr[inner_start+1:close_paren].strip()
                
                # Check for ∧ or ∨ at top level of inner expression
                and_parts = _split_by_operator(inner, '∧')
                or_parts = _split_by_operator(inner, '∨')
                
                if len(and_parts) >= 2:
                    # ¬(P ∧ Q) → (¬P ∨ ¬Q)
                    normalized_parts = []
                    for part in and_parts:
                        norm_part = normalize_rec(part)
                        if norm_part.startswith('¬'):
                            normalized_parts.append(normalize_rec(norm_part[1:].strip()))
                        else:
                            normalized_parts.append(f"¬{norm_part}")
                    # Sort for determinism
                    normalized_parts.sort()
                    result = f"({' ∨ '.join(normalized_parts)})"
                    if result != expr:
                        return normalize_rec(result)
                
                if len(or_parts) >= 2:
                    # ¬(P ∨ Q) → (¬P ∧ ¬Q)
                    normalized_parts = []
                    for part in or_parts:
                        norm_part = normalize_rec(part)
                        if norm_part.startswith('¬'):
                            normalized_parts.append(normalize_rec(norm_part[1:].strip()))
                        else:
                            normalized_parts.append(f"¬{norm_part}")
                    normalized_parts.sort()
                    result = f"({' ∧ '.join(normalized_parts)})"
                    if result != expr:
                        return normalize_rec(result)
        
        # Rule 3: Quantifier negation
        # ¬∃ (x : T), P → ∀ (x : T), ¬P
        neg_exists_match = re.match(r'^¬\s*∃\s*\(([^)]+)\)\s*,\s*(.+)$', expr)
        if neg_exists_match:
            binder = neg_exists_match.group(1).strip()
            body = neg_exists_match.group(2).strip()
            norm_body = normalize_rec(body)
            if norm_body.startswith('¬'):
                norm_body = normalize_rec(norm_body[1:].strip())
            else:
                norm_body = f"¬{norm_body}"
            return normalize_rec(f"∀ ({binder}), {norm_body}")
        
        # ¬∀ (x : T), P → ∃ (x : T), ¬P
        neg_forall_match = re.match(r'^¬\s*∀\s*\(([^)]+)\)\s*,\s*(.+)$', expr)
        if neg_forall_match:
            binder = neg_forall_match.group(1).strip()
            body = neg_forall_match.group(2).strip()
            norm_body = normalize_rec(body)
            if norm_body.startswith('¬'):
                norm_body = normalize_rec(norm_body[1:].strip())
            else:
                norm_body = f"¬{norm_body}"
            return normalize_rec(f"∃ ({binder}), {norm_body}")
        
        # Handle quantifiers FIRST (before implications) to avoid infinite recursion
        # Process body recursively, which may contain implications
        quant_match = re.match(r'^(∀|∃)\s*\(([^)]+)\)\s*,\s*(.+)$', expr)
        if quant_match:
            quant = quant_match.group(1)
            binder = quant_match.group(2).strip()
            body = quant_match.group(3).strip()
            
            # Rule 9: Binder normalization - flatten nested quantifiers of the same type
            # Check if body starts with the same quantifier
            nested_quant_match = re.match(r'^(∀|∃)\s*\(([^)]+)\)\s*,\s*(.+)$', body)
            if nested_quant_match and nested_quant_match.group(1) == quant:
                # Found nested quantifier of same type: ∀ (x : T), ∀ (y : U), P
                # Normalize to: ∀ (x : T) (y : U), P
                inner_binder = nested_quant_match.group(2).strip()
                inner_body = nested_quant_match.group(3).strip()
                # Combine binders: (x : T) and (y : U) -> (x : T) (y : U)
                combined_binder = f"{binder}) ({inner_binder}"
                norm_body = normalize_rec(inner_body)
                result = f"{quant} ({combined_binder}), {norm_body}"
                if result != expr:
                    return normalize_rec(result)
            
            # Normalize the body (which may contain implications, quantifiers, etc.)
            norm_body = normalize_rec(body)
            result = f"{quant} ({binder}), {norm_body}"
            if result != expr:
                return result
        
        # Rule 4: Contrapositive: P → Q → ¬Q → ¬P
        # Only apply to implications WITHOUT quantifiers to avoid infinite recursion
        # Quantifiers are handled above, so any quantifiers in implication parts are already processed
        impl_parts = _split_by_operator(expr, '→')
        if len(impl_parts) >= 2:
            # Check if any part contains quantifiers - if so, skip contrapositive
            # (quantifiers should have been processed already by the code above)
            has_quantifiers = False
            for part in impl_parts:
                if '∀' in part or '∃' in part:
                    has_quantifiers = True
                    break
            
            # Skip contrapositive if quantifiers are present (they cause recursion issues)
            # Just normalize the parts and return
            if has_quantifiers:
                normalized_parts = [normalize_rec(p) for p in impl_parts]
                result = ' → '.join(normalized_parts)
                if result != expr:
                    return result
                return expr
            
            # Apply contrapositive only for simple implications (no quantifiers)
            if len(impl_parts) == 2:
                # Single implication: P → Q becomes ¬Q → ¬P
                left = normalize_rec(impl_parts[0])
                right = normalize_rec(impl_parts[1])
                
                # Check if already in contrapositive form (right side negated)
                right_negated = right.startswith('¬')
                left_negated = left.startswith('¬')
                
                # If already in contrapositive form (right negated), we're done
                if right_negated:
                    # Ensure left is also negated for canonical form
                    if not left_negated:
                        left = f"¬{left}"
                    return f"{right} → {left}"
                
                # Convert to contrapositive: P → Q becomes ¬Q → ¬P
                neg_right = f"¬{right}"
                neg_left = f"¬{left}" if not left_negated else left
                
                # Don't recurse - return the contrapositive form
                return f"{neg_right} → {neg_left}"
            else:
                # Multiple implications: normalize each part, then convert chain
                # For simplicity, just normalize parts without full contrapositive conversion
                # (full contrapositive of chains is complex and can cause recursion)
                normalized_parts = [normalize_rec(p) for p in impl_parts]
                return ' → '.join(normalized_parts)
        
        # Rule 5a: Associativity - flatten nested ∧ and ∨ structures
        for op in ['∧', '∨']:
            parts = _split_by_operator(expr, op)
            if len(parts) >= 2:
                # Flatten nested structures: if any part is a parenthesized expression
                # with the same operator at top level, extract its operands
                flattened_parts = []
                for part in parts:
                    part_stripped = part.strip()
                    # Check if part is parenthesized and contains the same operator at top level
                    if part_stripped.startswith('(') and part_stripped.endswith(')'):
                        inner = part_stripped[1:-1].strip()
                        inner_parts = _split_by_operator(inner, op)
                        if len(inner_parts) >= 2:
                            # Flatten: add inner operands directly
                            flattened_parts.extend(inner_parts)
                        else:
                            flattened_parts.append(part)
                    else:
                        flattened_parts.append(part)
                
                # If we flattened anything, recurse
                if len(flattened_parts) > len(parts):
                    return normalize_rec(f" {op} ".join(flattened_parts))
        
        # Rule 5b: Commutativity - normalize order of ∧ and ∨ operands
        for op in ['∧', '∨']:
            parts = _split_by_operator(expr, op)
            if len(parts) >= 2:
                # Normalize each part and sort lexicographically
                normalized_parts = [normalize_rec(p) for p in parts]
                sorted_parts = sorted(normalized_parts)  # Lexicographic sort for determinism
                # Only apply if order actually changed
                if normalized_parts != sorted_parts:
                    return normalize_rec(f" {op} ".join(sorted_parts))
                # If already sorted, just return the normalized version
                result = f" {op} ".join(normalized_parts)
                if result != expr:
                    return normalize_rec(result)
        
        # Handle parenthesized expressions
        if expr.startswith('(') and expr.endswith(')'):
            inner = expr[1:-1].strip()
            normalized_inner = normalize_rec(inner)
            result = f"({normalized_inner})"
            if result != expr:
                return result
        
        # No transformation applies, return as-is
        return expr
    
    # Apply normalization recursively
    result = normalize_rec(s)
    return result

def _normalize_s1(s: str) -> str:
    """
    S1 normalization: Notation-level equalities that are definitionally equivalent.
    
    Rules are documented in the source of truth: bank/s1_rules.md
    
    Rules are applied in order:
    0. Alpha-renaming: Normalize bound variable names to canonical form (x₁, x₂, ...)
    1. x ≠ y → ¬ (x = y)  (definitional: ≠ is notation for ¬ (=))
    2. a ≥ b → b ≤ a      (definitional: ≥ is notation for flipped ≤)
    3. Logical equivalences (applied recursively):
       - Double negation: ¬¬P → P
       - De Morgan: ¬(P ∧ Q) → (¬P ∨ ¬Q), ¬(P ∨ Q) → (¬P ∧ ¬Q)
       - Quantifier negation: ¬∃ (x : T), P → ∀ (x : T), ¬P, ¬∀ (x : T), P → ∃ (x : T), ¬P
       - Contrapositive: P → Q → ¬Q → ¬P
       - Associativity: Flatten nested ∧ and ∨ structures: (P ∧ Q) ∧ R → P ∧ Q ∧ R
       - Commutativity: Normalize order of ∧ and ∨ operands (lexicographic)
       - Binder normalization: Flatten nested quantifiers of same type: ∀ (x : T), ∀ (y : U), P → ∀ (x : T) (y : U), P
    
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
    
    # Rule 3: Logical structure normalization (applied recursively)
    s = _normalize_logical_structure(s)
    
    # Re-run alpha-renaming after binder normalization to fix variable names
    # (binder normalization may combine scopes, creating duplicate variable names)
    s = _alpha_rename(s)
    
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
