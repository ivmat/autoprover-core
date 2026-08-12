/-
  AutoproverCorpus.Reliability.CoherentSystemBounds

  For a coherent (monotone, non-degenerate) structure function `phi` over `n` components, the
  series system (up iff EVERY component is up) and the parallel system (up iff SOME component
  is up) bound `phi` pointwise, at every component state `x`:
    series x ≤ phi x ≤ parallel x.
  This is the general n-component pointwise bound. It is distinct from the two results already
  in this corpus: `PivotalDecomposition` bounds `phi` only at the two CONSTANT extreme states
  (all-down, all-up); `KOutOfN` studies one specific family of structure functions (the
  k-out-of-n threshold systems). Here `series`/`parallel` are themselves just the two extreme
  members of that family (n-out-of-n and 1-out-of-n), used as a bracket around every OTHER
  coherent `phi`, at every state, not just the extreme ones.

  TERMINOLOGY (stated precisely, since the name is a claim): here "coherent" means monotone
  and non-degenerate (`phi` all-up = up, all-down = down) — the `Coherent` predicate reused
  from `PivotalDecomposition`. Much of the modern reliability literature reserves "coherent"
  for the STRONGER notion that additionally requires every component to be RELEVANT (pivotal
  in at least one state), and calls the monotone+non-degenerate class "semicoherent". The
  series/parallel bounds proved here hold for that broader semicoherent class, hence a
  fortiori for every classical (relevance-requiring) coherent system; nothing below relies on
  a relevance hypothesis.

  Attribution: Classical reliability theory (Barlow and Proschan, 1975).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Reliability.PivotalDecomposition

namespace AutoproverCorpus.CoherentSystemBounds

open AutoproverCorpus.PivotalDecomposition

/-! ### The series and parallel structure functions, over `n` components -/

/-- The series structure function: up iff EVERY component is up. -/
def seriesPhi {n : Nat} (x : Fin n → Bool) : Bool :=
  (List.finRange n).all (fun i => x i)

/-- The parallel structure function: up iff SOME component is up. -/
def parallelPhi {n : Nat} (x : Fin n → Bool) : Bool :=
  (List.finRange n).any (fun i => x i)

theorem seriesPhi_iff {n : Nat} (x : Fin n → Bool) :
    seriesPhi x = true ↔ ∀ i, x i = true := by
  unfold seriesPhi
  rw [List.all_eq_true]
  exact ⟨fun h i => h i (List.mem_finRange i), fun h i _ => h i⟩

theorem parallelPhi_iff {n : Nat} (x : Fin n → Bool) :
    parallelPhi x = true ↔ ∃ i, x i = true := by
  unfold parallelPhi
  rw [List.any_eq_true]
  exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, List.mem_finRange i, hi⟩⟩

/-! ### The pointwise bound -/

/-- **Lower bound.** If the series system is up at `x` (every component up), any coherent
    `phi` is up at `x` too — this is exactly `coherent_all_true` from `PivotalDecomposition`,
    read through `seriesPhi_iff`. Stated with core Lean's `Bool` order (`a ≤ b ↔ (a = true →
    b = true)`), matching the classical pointwise inequality directly. -/
theorem coherent_series_le_phi {n : Nat} {phi : (Fin n → Bool) → Bool}
    (hc : Coherent phi) (x : Fin n → Bool) : seriesPhi x ≤ phi x := by
  intro hs
  exact coherent_all_true hc x ((seriesPhi_iff x).mp hs)

/-- **Upper bound.** If any coherent `phi` is up at `x`, the parallel system is up at `x` too
    (some component must be up) — exactly `coherent_true_imp_exists` from
    `PivotalDecomposition`, read through `parallelPhi_iff`. -/
theorem coherent_phi_le_parallel {n : Nat} {phi : (Fin n → Bool) → Bool}
    (hc : Coherent phi) (x : Fin n → Bool) : phi x ≤ parallelPhi x := by
  intro hphi
  exact (parallelPhi_iff x).mpr (coherent_true_imp_exists hc x hphi)

/-- **Coherent-system bound (main theorem).** For any coherent structure function `phi`, at
    EVERY component state `x` (not just the two constant extremes): `series x ≤ phi x ≤
    parallel x`. -/
theorem coherent_series_le_phi_le_parallel {n : Nat} {phi : (Fin n → Bool) → Bool}
    (hc : Coherent phi) (x : Fin n → Bool) :
    seriesPhi x ≤ phi x ∧ phi x ≤ parallelPhi x :=
  ⟨coherent_series_le_phi hc x, coherent_phi_le_parallel hc x⟩

/-! ### Instance: a genuine 3-component majority system, strictly between series and parallel -/

/-- 2-out-of-3 majority, written out directly (not via the `KOutOfN` module): up iff some PAIR
    of the three components is up. -/
def majority3 (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

theorem majority3_monotone : Monotone majority3 := by
  intro x y h hx
  unfold majority3 at hx ⊢
  simp only [Bool.or_eq_true_iff, Bool.and_eq_true_iff] at hx
  simp only [Bool.or_eq_true_iff, Bool.and_eq_true_iff]
  rcases hx with (⟨h0, h1⟩ | ⟨h1, h2⟩) | ⟨h0, h2⟩
  · exact Or.inl (Or.inl ⟨h 0 h0, h 1 h1⟩)
  · exact Or.inl (Or.inr ⟨h 1 h1, h 2 h2⟩)
  · exact Or.inr ⟨h 0 h0, h 2 h2⟩

theorem majority3_coherent : Coherent majority3 :=
  { mono := majority3_monotone
    allFalse := by decide
    allTrue := by decide }

/-- Components `0` and `1` up, component `2` down. -/
def xTTF : Fin 3 → Bool := fun i => i.val ≠ 2

/-- Only component `0` up. -/
def xTFF : Fin 3 → Bool := fun i => i.val = 0

/-- **Non-vacuity, lower bound.** At `xTTF`, the series system is DOWN (component `2` is
    down) while `majority3` is genuinely UP (components `0` and `1` suffice): the lower bound
    is not forced to be an equality. -/
example : seriesPhi xTTF = false ∧ majority3 xTTF = true := by decide

/-- **Non-vacuity, upper bound.** At `xTFF`, `majority3` is DOWN (no pair of components is
    up) while the parallel system is genuinely UP (component `0` alone suffices): the upper
    bound is not forced to be an equality either. -/
example : majority3 xTFF = false ∧ parallelPhi xTFF = true := by decide

/-- The bound theorem applied concretely at `xTTF`, for the genuinely intermediate
    `majority3` system. -/
example :
    seriesPhi xTTF ≤ majority3 xTTF ∧ majority3 xTTF ≤ parallelPhi xTTF :=
  coherent_series_le_phi_le_parallel majority3_coherent xTTF

end AutoproverCorpus.CoherentSystemBounds
