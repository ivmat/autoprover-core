"""The kernel gate: a checker as a sound oracle (ARCHITECTURE.md §4).

A candidate is never accepted on the strength of the prover's own claim
about it — only a checker process's exit status counts. This module
wraps an *injectable* checker command so the gate is not tied to any one
proof system: the default wiring happens to invoke Lean, because that is
what this repository's corpus is written in, but `KernelGate` itself
knows nothing about Lean syntax or semantics. Any command that reports
acceptance/rejection via its exit status can be plugged in through the
`checker_command` parameter.

The gate also enforces, in code rather than only in the schema, the
kernel-vs-model-checker distinction from ARCHITECTURE.md §4: a
`kind="kernel"` gate refuses to accept a harness/bound/env_assumptions
triple (a proof kernel's verdict is not relative to any of those), and a
`kind="model-checker"` gate refuses to omit them (its verdict is only
valid relative to that triple, never portable the way a kernel's
re-runnable proof object is).
"""

from __future__ import annotations

import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Optional, Sequence, Union

from .receipts import Certificate, Checker, Obligation, Receipt, now_iso

__all__ = [
    "CheckerResult",
    "CheckerCommand",
    "lean_checker_command",
    "KernelGate",
]


@dataclass(frozen=True)
class CheckerResult:
    """What a pluggable checker command reports back to the gate. The
    gate trusts nothing here except `accepted` (derived from the
    process's own exit status by the command implementation) and the
    optional per-obligation detail; `stdout`/`stderr` are kept only for
    diagnostics, never interpreted as part of the verdict.
    """

    accepted: bool
    exit_code: int
    stdout: str = ""
    stderr: str = ""
    # Optional per-obligation status detail a richer checker (e.g. a
    # model checker that can report per-property coverage) may supply.
    # A plain kernel invocation (a whole-file accept/reject) typically
    # leaves this None, and the gate falls back to reducing every
    # requested obligation to the file-level verdict.
    obligation_statuses: Optional[dict] = None


# A checker command takes the candidate file path and returns a result.
# This is the entire seam the gate depends on — swap this out and the
# gate works against any checker, Lean or otherwise.
CheckerCommand = Callable[[Path], CheckerResult]


def lean_checker_command(
    lean_executable: str = "lean", extra_args: Sequence[str] = ()
) -> CheckerCommand:
    """Default checker command: runs ``lean <extra_args...> <file>`` and
    treats a zero exit code as kernel acceptance. This is *a* default
    value for `checker_command`, not machinery baked into `KernelGate` —
    nothing in this module besides this one function knows what "lean"
    is. Pass `extra_args=("--", ...)` or point `lean_executable` at
    ``lake env lean`` (as a shell wrapper) for a project that needs its
    dependencies on the path; both are just different argv choices for a
    subprocess call.
    """

    def run(file_path: Path) -> CheckerResult:
        cmd = [lean_executable, *extra_args, str(file_path)]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        return CheckerResult(
            accepted=(proc.returncode == 0),
            exit_code=proc.returncode,
            stdout=proc.stdout,
            stderr=proc.stderr,
        )

    return run


class KernelGate:
    """Wraps a checker command as a sound oracle and emits a Receipt.

    Never treats the prover's own claim as a verdict: `check()` invokes
    `checker_command` and reads the resulting `CheckerResult.accepted`
    (which the command implementation must derive from the checker
    process's own exit status), and nothing else determines the verdict.
    """

    def __init__(
        self,
        *,
        checker_command: CheckerCommand,
        checker_name: str,
        checker_version: str,
        kind: str = "kernel",
        toolchain_id: str,
    ):
        if kind not in ("kernel", "model-checker"):
            raise ValueError(f"kind must be 'kernel' or 'model-checker', got {kind!r}")
        self.checker_command = checker_command
        self.checker_name = checker_name
        self.checker_version = checker_version
        self.kind = kind
        self.toolchain_id = toolchain_id

    def check(
        self,
        *,
        target_id: str,
        candidate_id: str,
        candidate_file: Union[str, Path],
        obligation_ids: Sequence[str] = (),
        harness: Optional[str] = None,
        bound: Optional[Union[str, float, int]] = None,
        env_assumptions: Optional[str] = None,
    ) -> Receipt:
        """Run the checker on ``candidate_file`` and produce a Receipt.

        For a `kind="kernel"` gate, `harness`/`bound`/`env_assumptions`
        must all be omitted (a kernel's verdict is not relative to any
        of those). For a `kind="model-checker"` gate they are all
        required, and are recorded on the receipt so its verdict's
        scope is explicit (ARCHITECTURE.md §4).
        """
        candidate_file = Path(candidate_file)

        if self.kind == "kernel":
            if harness is not None or bound is not None or env_assumptions is not None:
                raise ValueError(
                    "a kernel gate does not accept harness/bound/env_assumptions"
                )
        else:
            if not harness or bound is None or not env_assumptions:
                raise ValueError(
                    "a model-checker gate requires harness, bound, and env_assumptions"
                )

        result = self.checker_command(candidate_file)
        verdict = "accepted" if result.accepted else "rejected"

        certificate = None
        if self.kind == "kernel" and verdict == "accepted":
            certificate = Certificate(
                checked_file=str(candidate_file), toolchain_id=self.toolchain_id
            )

        ids = tuple(obligation_ids) or (target_id,)
        if result.obligation_statuses:
            obligations = tuple(
                Obligation(id=oid, status=result.obligation_statuses.get(
                    oid, "held" if verdict == "accepted" else "failed"
                ))
                for oid in ids
            )
        else:
            # A plain whole-file kernel/model-checker run only tells us
            # the file-level verdict; every requested obligation is
            # reduced to that same held/failed status. Distinguishing
            # "vacuous" or "not-exercised" at the obligation level
            # requires a checker that reports per-obligation detail
            # (via `obligation_statuses`) — the audit layer (audit.py)
            # is where vacuity is actually detected in this reference
            # implementation.
            status = "held" if verdict == "accepted" else "failed"
            obligations = tuple(Obligation(id=oid, status=status) for oid in ids)

        return Receipt(
            target_id=target_id,
            candidate_id=candidate_id,
            checker=Checker(kind=self.kind, name=self.checker_name, version=self.checker_version),
            verdict=verdict,
            certificate=certificate,
            harness=harness if self.kind == "model-checker" else None,
            bound=bound if self.kind == "model-checker" else None,
            env_assumptions=env_assumptions if self.kind == "model-checker" else None,
            obligations=obligations,
            produced_at=now_iso(),
        )
