"""Helper module to generate Lean scripts that pretty-print expressions with pinned PP options."""

import re

# Strict tier PP options profile
# These options ensure deterministic pretty-printing across machines
# Documented in PP_PROFILE.md
STRICT_PP_OPTIONS = {
    "pp.notation": "true",      # Use notations (→, ↔, ∀, ∃, etc.)
    "pp.foralls": "true",       # Show forall quantifiers explicitly
    "pp.parens": "true",        # Add parentheses where needed
    "pp.unicode": "true",       # Use Unicode characters
    "pp.implicit": "false",     # Hide implicit arguments
    "pp.explicit": "false",     # Hide explicit type annotations
}

def generate_pretty_print_script(imports: list[str], prop: str) -> str:
    """Generate a Lean script that pretty-prints a proposition with strict PP options.
    
    Args:
        imports: List of import statements
        prop: The proposition to pretty-print
        
    Returns:
        A Lean script that sets PP options and outputs the pretty-printed proposition
    """
    lines = []
    
    # Handle import mapping
    import_map = {
        "Mathlib.Algebra.Divisibility": "Mathlib.Algebra.Divisibility.Basic"
    }
    
    # Add imports
    for imp in imports:
        normalized_imp = imp.replace("/", ".")
        normalized_imp = import_map.get(normalized_imp, normalized_imp)
        lines.append(f"import {normalized_imp}")
    
    lines.append("")
    
    # Set strict PP options (must be set before defining the proposition)
    for option, value in STRICT_PP_OPTIONS.items():
        lines.append(f"set_option {option} {value}")
    
    lines.append("")
    
    # Define the proposition
    lines.append("def _prop : Prop :=")
    lines.append(f"  {prop}")
    lines.append("")
    
    # Use #print to output the definition
    # This will show: "def _prop : Prop := <pretty-printed expression>"
    lines.append("#print _prop")
    
    return "\n".join(lines)

def parse_pretty_printed_output(lean_output: str) -> str:
    """Parse the pretty-printed expression from Lean's #print output.
    
    Args:
        lean_output: The stdout/stderr output from Lean
        
    Returns:
        The pretty-printed expression, or empty string if not found
    """
    # #print output format can vary, but typically:
    # "def _prop : Prop := <expression>"
    # or multi-line with the expression on following lines
    
    # Split output into lines for easier processing
    lines = lean_output.split('\n')
    
    # Find the line containing "def _prop : Prop :="
    def_start_idx = None
    for i, line in enumerate(lines):
        if 'def _prop : Prop :=' in line:
            def_start_idx = i
            break
    
    if def_start_idx is None:
        # Try regex patterns as fallback
        patterns = [
            # Pattern 1: "def _prop : Prop := <expr>"
            r"def _prop : Prop\s*:=\s*(.+?)(?:\n\n|\Z)",
            # Pattern 2: Just the expression after ":="
            r":=\s*((?:(?!\n\n)[\s\S])+)",
        ]
        
        for pattern in patterns:
            match = re.search(pattern, lean_output, re.DOTALL)
            if match:
                expr = match.group(1).strip()
                # Clean up: normalize whitespace
                expr = re.sub(r'\s+', ' ', expr)
                expr = expr.strip()
                if expr:
                    return expr
        return ""
    
    # Extract the expression part from the definition line
    def_line = lines[def_start_idx]
    if ':=' in def_line:
        # Expression might be on the same line or following lines
        parts = def_line.split(':=', 1)
        if len(parts) == 2:
            expr_part = parts[1].strip()
            if expr_part:
                # Expression is on the same line
                return expr_part
    
    # Expression is on following lines
    # Collect lines until we hit an empty line or another definition
    expr_lines = []
    for i in range(def_start_idx + 1, len(lines)):
        line = lines[i].strip()
        # Stop at empty line or new definition
        if not line or line.startswith('def ') or line.startswith('theorem '):
            break
        # Skip comments
        if line.startswith('--'):
            continue
        expr_lines.append(line)
    
    if expr_lines:
        # Join lines and normalize whitespace
        expr = ' '.join(expr_lines)
        expr = re.sub(r'\s+', ' ', expr)
        return expr.strip()
    
    return ""

