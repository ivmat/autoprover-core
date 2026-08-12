#!/usr/bin/env python3
"""Worked end-to-end example: drives two tiny, self-contained Lean
targets through the full reference pipeline (queue -> kernel_gate ->
audit -> ratchet) and prints what happened at each boundary.

  - `lean/Genuine.lean`  — a genuinely-true, non-vacuous theorem.
  - `lean/Vacuous.lean`  — a vacuously-true theorem (ARCHITECTURE.md §5's
    failure mode).

Both are accepted by the Lean kernel. The point of this example is that
the kernel gate alone cannot tell them apart — both come back
`verdict: accepted` — and the semantic audit layer is what flags the
vacuous one. See README.md in this directory for the walkthrough and
the exact receipts this produces.

This script invokes the real `lean` executable on exactly these two
small, single files — nothing else. It never touches `corpus/` and never
runs `lake build`. If `lean` is not on PATH, it explains that and exits
without running the Lean-backed part (the rest of the reference
implementation's test suite runs with no Lean installation at all - see
`reference/tests/`).
"""

from __future__ import annotations

import shutil
import sys
from pathlib import Path

EXAMPLES_DIR = Path(__file__).resolve().parent
REFERENCE_DIR = EXAMPLES_DIR.parent
sys.path.insert(0, str(REFERENCE_DIR))

from autoprover_ref.audit import TargetProvenance  # noqa: E402
from autoprover_ref.kernel_gate import KernelGate, lean_checker_command  # noqa: E402
from autoprover_ref.pipeline import Pipeline  # noqa: E402
from autoprover_ref.queue import TargetQueue  # noqa: E402
from autoprover_ref.ratchet import Ratchet  # noqa: E402


def main() -> int:
    lean_executable = shutil.which("lean")
    if lean_executable is None:
        print(
            "`lean` was not found on PATH — skipping the Lean-backed run.\n"
            "To run this example once Lean is available:\n"
            "  1. Install the toolchain pinned in corpus/lean-toolchain "
            "(leanprover/lean4:v4.31.0).\n"
            "  2. Run `python3 reference/examples/run_example.py` again.\n"
            "The kernel gate's checker command is fully injectable (see "
            "kernel_gate.KernelGate) - swapping `lean_checker_command()` for any "
            "other checker wiring does not require touching pipeline.py, queue.py, "
            "audit.py, or ratchet.py.\n"
            "All of reference/tests/ runs with no Lean installed at all."
        )
        return 0

    run_dir = EXAMPLES_DIR / "_run"
    run_dir.mkdir(exist_ok=True)
    receipts_dir = run_dir / "receipts"

    gate = KernelGate(
        checker_command=lean_checker_command(lean_executable),
        checker_name="lean",
        checker_version=_lean_version(lean_executable),
        kind="kernel",
        toolchain_id="leanprover/lean4:v4.31.0",
    )
    pipeline = Pipeline(
        queue=TargetQueue(run_dir / "queue.jsonl"),
        gate=gate,
        ratchet=Ratchet(run_dir / "ratchet.jsonl"),
        receipts_dir=receipts_dir,
    )

    genuine_provenance = TargetProvenance(
        source="reference/examples/lean/Genuine.lean",
        statement_text=(
            "theorem nonempty_has_length_ge_one (l : List Nat) (h : 0 < l.length) : "
            "1 <= l.length"
        ),
        claim_keywords=(),
        preconditions=("0 < l.length",),
        non_vacuity_witness="nonempty_witness : 0 < ([1] : List Nat).length, checked by decide",
    )
    vacuous_provenance = TargetProvenance(
        source="reference/examples/lean/Vacuous.lean",
        statement_text=(
            "theorem falsely_sorted_claim (l : List Nat) (h : l.length < 0) : Sorted l"
        ),
        claim_keywords=("sorted",),
        preconditions=("l.length < 0",),
        non_vacuity_witness=None,  # honestly: none exists, l.length < 0 is unsatisfiable
    )

    print("=== target: genuine (nonempty_has_length_ge_one) ===")
    genuine_result = pipeline.run_target(
        target_id="genuine",
        candidate_id="genuine-v1",
        candidate_file=EXAMPLES_DIR / "lean" / "Genuine.lean",
        provenance=genuine_provenance,
    )
    _report(genuine_result)

    print("\n=== target: vacuous (falsely_sorted_claim) ===")
    vacuous_result = pipeline.run_target(
        target_id="vacuous",
        candidate_id="vacuous-v1",
        candidate_file=EXAMPLES_DIR / "lean" / "Vacuous.lean",
        provenance=vacuous_provenance,
    )
    _report(vacuous_result)

    print(f"\nReceipts written under: {receipts_dir}")
    print(f"Ratchet accepted set:   {sorted(pipeline.ratchet.accepted_targets)}")

    ok = (
        genuine_result.kernel_receipt.verdict == "accepted"
        and genuine_result.audit_verdict.verdict == "pass"
        and genuine_result.final_state == "accepted"
        and vacuous_result.kernel_receipt.verdict == "accepted"
        and vacuous_result.audit_verdict.verdict == "fail"
        and vacuous_result.audit_verdict.failure_reason == "vacuous-precondition"
        and vacuous_result.final_state == "queued"
    )
    print(f"\nExpected pattern observed (kernel accepts both, audit flags only the vacuous "
          f"one): {ok}")
    return 0 if ok else 1


def _lean_version(lean_executable: str) -> str:
    import subprocess

    proc = subprocess.run([lean_executable, "--version"], capture_output=True, text=True)
    return proc.stdout.strip() or "unknown"


def _report(result) -> None:
    print(f"  kernel verdict: {result.kernel_receipt.verdict}")
    if result.kernel_receipt.certificate:
        print(f"  certificate:    {result.kernel_receipt.certificate.to_dict()}")
    if result.audit_verdict is not None:
        print(f"  audit verdict:  {result.audit_verdict.verdict}"
              + (f" ({result.audit_verdict.failure_reason})"
                 if result.audit_verdict.failure_reason else ""))
    print(f"  final state:    {result.final_state}")


if __name__ == "__main__":
    raise SystemExit(main())
