/-
  Example.Genuine

  A genuinely-true, non-vacuous theorem — one half of the reference
  pipeline's worked end-to-end example (see reference/examples/README.md).
  The claim made is exactly the theorem statement below, as accepted by
  the Lean kernel; the hypothesis is genuinely satisfiable, and
  `nonempty_witness` is the concrete instance that shows it (this is
  exactly the "non-vacuity witness" the audit layer in
  `reference/autoprover_ref/audit.py` looks for).

  This file is a small synthetic example written for this repository —
  it is not drawn from `corpus/` or any external source, and it is a
  single, isolated file: it must never be pulled into a `lake build`
  over `corpus/`.

  Machine-checked in Lean 4 (core language, no external libraries), in
  the same zero-dependency style as `corpus/`.
-/

namespace AutoproverExample

/-- If a list has at least one element, its length is at least 1. This
    is genuinely conditional — the hypothesis `0 < l.length` is
    satisfiable, and the theorem's content matches what its name claims:
    nothing here overclaims beyond "non-empty implies length >= 1". -/
theorem nonempty_has_length_ge_one (l : List Nat) (h : 0 < l.length) : 1 ≤ l.length := h

/-- Non-vacuity witness for the precondition above: a concrete list for
    which `0 < l.length` actually holds, checked by `decide`. Recording
    a witness like this is what lets the semantic audit layer
    distinguish this target from `Vacuous.lean`'s. -/
theorem nonempty_witness : 0 < ([1] : List Nat).length := by decide

end AutoproverExample
