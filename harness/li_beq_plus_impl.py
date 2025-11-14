"""LeanInteract BEq+ helpers.

This module vendors the BEqL/BEq+ reference implementation from
https://github.com/augustepoiroux/LeanInteract (commit
90a052c63eddacbd434269f049280d06e41a7a36). The upstream code is MIT
licensed; see that repository for full context and citation details.
The version below trims CLI/demo helpers and replaces the rich console
output with simple prints so it can run inside the SAF harness without
extra dependencies.
"""

from __future__ import annotations

import json
import sys

from lean_interact import AutoLeanServer, Command, LeanREPLConfig  # type: ignore
from lean_interact.interface import (  # type: ignore
    CommandResponse,
    LeanError,
    Pos,
    message_intersects_code,
)
from lean_interact.utils import (  # type: ignore
    clean_last_theorem_string,
    indent_code,
    split_conclusion,
)


def _verbose_print(verbose: bool, *args: object) -> None:
    if verbose:
        print(*args)


def _log_error(*args: object) -> None:
    print(*args, file=sys.stderr)


def extract_exact_proof(
    lean_output: CommandResponse,
    proof_start_line: int | None = None,
) -> str | None:
    """Extract the proof returned by `exact?` if Lean emits a suggestion."""
    start = Pos(line=proof_start_line, column=0) if proof_start_line else None
    for message in lean_output.messages:
        if message_intersects_code(message, start, None):
            if message.severity == "error":
                return None
            if message.severity == "info" and message.data.startswith("Try this:"):
                return message.data.split("Try this:")[1].strip()
    return None


def check_proof_sub(
    server: AutoLeanServer,
    formal_code: str,
    context_env: int,
    formal_2_start_line: int,
    proof: str,
    timeout: int,
    indent_level: int = 2,
) -> str | None:
    """
    Run Lean code appended with a given proof and check its validity.

    Args:
        server: Instance of AutoLeanServer.
        formal_code: Concatenated Lean formalizations.
        context_env: Execution environment from the Lean server.
        formal_2_start_line: Starting line number of the second formalization.
        proof: Proof tactic string to run.
        timeout: Timeout in seconds for the Lean server execution.
        indent_level: Indentation level for the proof block.

    Returns:
        The proof string (or an extracted exact proof) if valid; None otherwise.
    """
    prepended = "\nintros\nsymm_saturate\n"
    try:
        lean_output = server.run(
            Command(
                cmd=formal_code + indent_code(prepended + proof, indent_level),
                env=context_env,
            ),
            timeout=timeout,
        )
        if isinstance(lean_output, LeanError):
            return None
        if proof == "sorry":
            if lean_output.lean_code_is_valid(start_pos=Pos(line=formal_2_start_line, column=0)):
                return proof
            return None

        if lean_output.lean_code_is_valid(
            start_pos=Pos(line=formal_2_start_line, column=0),
            allow_sorry=False,
        ):
            if proof == "exact?":
                return extract_exact_proof(lean_output, proof_start_line=formal_2_start_line)
            return proof
    except TimeoutError:
        pass
    except (ConnectionAbortedError, json.JSONDecodeError) as exc:  # pragma: no cover - transport noise
        _log_error(f"Error during proof checking: {exc}")
    return None


def beql(
    formalization_1: str,
    formalization_2: str,
    src_header: str,
    repl_config: LeanREPLConfig,
    timeout_per_proof: int,
    verbose: bool = False,
) -> bool:
    """
    Check equivalence of two formalizations using the BEq_L metric.

    Returns:
        True if both directions of the equivalence hold; False otherwise.
    """
    server = AutoLeanServer(config=repl_config)
    context_run = server.run(Command(cmd=src_header), add_to_session_cache=True)
    assert isinstance(context_run, CommandResponse)
    context_env = context_run.env

    base_thm_name = "base_theorem"
    reformulated_thm_name = "reformulated_theorem"

    res = [False, False]
    for i, (base_thm, reform_thm) in enumerate(
        [(formalization_1, formalization_2), (formalization_2, formalization_1)]
    ):
        _verbose_print(verbose, f"=====\nChecking {'1 -> 2' if i == 0 else '2 -> 1'}")
        try:
            formal_1_code = clean_last_theorem_string(base_thm, base_thm_name, add_sorry=True) + "\n\n"
            formal_2_start_line = formal_1_code.count("\n") + 1
            formal_2_code = f"{clean_last_theorem_string(reform_thm, reformulated_thm_name, add_sorry=False)} := by"
        except ValueError:
            _verbose_print(verbose, "Invalid theorems encountered, skipping this pair.")
            break

        formal_code = formal_1_code + formal_2_code
        if check_proof_sub(server, formal_code, context_env, formal_2_start_line, "sorry", timeout_per_proof) is None:
            _verbose_print(verbose, "Ill-typed formalization encountered, skipping this pair.")
            break

        proof_exact = check_proof_sub(
            server, formal_code, context_env, formal_2_start_line, "exact?", timeout_per_proof
        )
        if proof_exact and base_thm_name in proof_exact:
            res[i] = True
            _verbose_print(verbose, "Proof exact")
            _verbose_print(verbose, proof_exact)
        else:
            break

    return res[0] and res[1]


def beq_plus(
    formalization_1: str,
    formalization_2: str,
    src_header: str,
    repl_config: LeanREPLConfig,
    timeout_per_proof: int,
    verbose: bool = False,
) -> bool:
    """
    Check equivalence of two formalizations using the BEq+ metric.

    Returns:
        True if both directions of the equivalence hold; False otherwise.
    """
    server = AutoLeanServer(config=repl_config)
    context_run = server.run(Command(cmd=src_header), add_to_session_cache=True)
    assert isinstance(context_run, CommandResponse)
    context_env = context_run.env

    base_thm_name = "base_theorem"
    reformulated_thm_name = "reformulated_theorem"

    def prove_all(tactics: list[str]) -> str:
        prove_independent = " ; ".join([f"(all_goals try {t})" for t in tactics])
        prove_combined = "all_goals (" + " ; ".join([f"(try {t})" for t in tactics]) + ")"
        return "all_goals intros\nfirst | (" + prove_independent + ") | (" + prove_combined + ")"

    solver_tactics_apply = ["tauto", "simp_all_arith!", "noncomm_ring", "exact?"]
    solver_tactics_have = ["tauto", "simp_all_arith!", "exact? using this"]
    proof_all_apply = prove_all(solver_tactics_apply)
    proof_all_have = prove_all(solver_tactics_have)

    res = [False, False]
    for i, (base_thm, reform_thm) in enumerate(
        [(formalization_1, formalization_2), (formalization_2, formalization_1)]
    ):
        _verbose_print(verbose, f"=====\nChecking {'1 -> 2' if i == 0 else '2 -> 1'}")
        try:
            formal_1_code = clean_last_theorem_string(base_thm, base_thm_name, add_sorry=True) + "\n\n"
            formal_2_start_line = formal_1_code.count("\n") + 1
            formal_2_code = f"{clean_last_theorem_string(reform_thm, reformulated_thm_name, add_sorry=False)} := by"
        except ValueError:
            _verbose_print(verbose, "Invalid theorem encountered, skipping this pair.")
            break

        formal_code = formal_1_code + formal_2_code
        if check_proof_sub(server, formal_code, context_env, formal_2_start_line, "sorry", timeout_per_proof) is None:
            _verbose_print(verbose, "Ill-typed formalization encountered, skipping this pair.")
            break

        proof_exact = check_proof_sub(
            server, formal_code, context_env, formal_2_start_line, "exact?", timeout_per_proof
        )
        if proof_exact and base_thm_name in proof_exact:
            res[i] = True
            _verbose_print(verbose, "Proof exact")
            _verbose_print(verbose, proof_exact)
            continue

        proof_apply = check_proof_sub(
            server,
            formal_code,
            context_env,
            formal_2_start_line,
            f"apply {base_thm_name}\n" + proof_all_apply,
            timeout_per_proof,
        )
        if proof_apply:
            res[i] = True
            _verbose_print(verbose, "Proof apply")
            _verbose_print(verbose, proof_apply)
            continue

        provable_without_have = False
        try:
            res_without_have = server.run(
                Command(cmd=formal_code + proof_all_have, env=context_env),
                timeout=timeout_per_proof,
            )
            if isinstance(res_without_have, CommandResponse):
                provable_without_have = res_without_have.lean_code_is_valid(allow_sorry=False)
        except TimeoutError:
            pass
        except (ConnectionAbortedError, json.JSONDecodeError) as exc:  # pragma: no cover - transport noise
            _log_error(f"Error during proof checking: {exc}")

        if not provable_without_have:
            idx_conclusion = split_conclusion(formal_1_code)
            if idx_conclusion:
                idx_end_conclusion = formal_1_code.rfind(":=")
                conclusion = formal_1_code[idx_conclusion:idx_end_conclusion].strip()
                have_stmt_proof = (
                    f"have {conclusion} := by\n"
                    + indent_code(f"apply_rules [{base_thm_name}]\n" + proof_all_apply, 2)
                    + "\n"
                )
                proof_have = check_proof_sub(
                    server,
                    formal_code,
                    context_env,
                    formal_2_start_line,
                    have_stmt_proof + proof_all_have,
                    timeout_per_proof,
                )
                if proof_have:
                    res[i] = True
                    _verbose_print(verbose, "Proof have")
                    _verbose_print(verbose, proof_have)
                    continue

        for max_step in range(0, 5):
            proof_convert = check_proof_sub(
                server,
                formal_code,
                context_env,
                formal_2_start_line,
                f"convert (config := .unfoldSameFun) {base_thm_name} using {max_step}\n" + proof_all_apply,
                timeout_per_proof,
            )
            if proof_convert:
                res[i] = True
                _verbose_print(verbose, "Proof convert")
                _verbose_print(verbose, proof_convert)
                break

        if not res[i]:
            break

    return res[0] and res[1]


__all__ = [
    "beql",
    "beq_plus",
    "check_proof_sub",
    "extract_exact_proof",
]
