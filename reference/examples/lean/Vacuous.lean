/-
  Example.Vacuous

  A vacuously-true theorem — the other half of the reference pipeline's
  worked end-to-end example (see reference/examples/README.md). This is
  exactly the ARCHITECTURE.md §5 vacuous-acceptance failure mode: its
  precondition (`l.length < 0`) can never hold for a `List Nat`, so the
  kernel *correctly* accepts the proof — the derivation really is valid
  — while the "theorem" says nothing about the world, because its
  interesting conclusion (`Sorted l`) is never actually exercised. The
  kernel gate in this reference implementation accepts this file exactly
  like `Genuine.lean`; the semantic audit layer is where the difference
  becomes visible (see run_example.py).

  `Sorted` is hand-rolled here rather than imported from an external
  library, in the same zero-dependency style as `corpus/`.

  This file is a small synthetic example written for this repository —
  it is not drawn from `corpus/` or any external source, and it is a
  single, isolated file: it must never be pulled into a `lake build`
  over `corpus/`.
-/

namespace AutoproverExample

/-- A minimal, self-contained "sortedness" predicate: every earlier
    index's element is `<=` every later index's element. -/
def Sorted (l : List Nat) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!

/-- Named and claimed as a sortedness result, but the precondition
    `l.length < 0` is unsatisfiable for `List Nat` (`Nat` has no
    negative values) — so this holds vacuously, for every list,
    without `Sorted` ever being genuinely exercised. A kernel-checked
    proof of this is real (the derivation is valid), but the claim it
    licenses is empty. -/
theorem falsely_sorted_claim (l : List Nat) (h : l.length < 0) : Sorted l :=
  absurd h (Nat.not_lt_zero l.length)

end AutoproverExample
