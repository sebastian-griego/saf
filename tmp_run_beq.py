from pathlib import Path
from harness.li_beq_plus_wrapper import run_beq_plus
print(run_beq_plus(Path('harness/lean_project'), 'True', 'True', 'import Mathlib', timeout_seconds=10))
