"""Function to run Lean pretty-printing with strict PP options."""

import subprocess
import tempfile
from pathlib import Path
from pretty_print_lean import generate_pretty_print_script, parse_pretty_printed_output

def run_lean_pretty_print(project_dir: Path, imports: list[str], prop: str, timeout: int = None) -> tuple[bool, str, str]:
    """Pretty-print a proposition using Lean with strict PP options.
    
    Args:
        project_dir: Path to Lean project directory
        imports: List of import statements
        prop: The proposition to pretty-print
        timeout: Timeout in seconds
        
    Returns:
        Tuple of (success: bool, pretty_printed_expr: str, stderr: str)
        If success is False, pretty_printed_expr will be empty.
    """
    # Generate the Lean script
    script = generate_pretty_print_script(imports, prop)
    
    # Write to temporary file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False, encoding='utf-8') as tmp_file:
        tmp_path = Path(tmp_file.name)
        tmp_file.write(script)
    
    try:
        # Run Lean
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp_path)],
            cwd=str(project_dir),
            capture_output=True,
            text=True,
            shell=False,
            timeout=timeout
        )
        
        # Combine stdout and stderr (Lean outputs to both)
        output = proc.stdout + proc.stderr
        
        if proc.returncode != 0:
            return (False, "", output)
        
        # Parse the pretty-printed expression
        pretty_printed = parse_pretty_printed_output(output)
        
        if not pretty_printed:
            # If parsing failed, return the raw output for debugging
            return (False, "", output)
        
        return (True, pretty_printed, output)
        
    except subprocess.TimeoutExpired:
        return (False, "", "Pretty-print timeout expired")
    finally:
        # Clean up the temporary file
        try:
            tmp_path.unlink()
        except OSError:
            pass

