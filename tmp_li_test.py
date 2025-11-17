from pathlib import Path
from harness.li_beq_plus_wrapper import make_lean_project_config
from lean_interact import AutoLeanServer, Command
config = make_lean_project_config(Path('harness/lean_project'), timeout_seconds=10)
server = AutoLeanServer(config=config)
resp = server.run(Command(cmd='import Mathlib'), add_to_session_cache=False)
print(resp.model_dump())
