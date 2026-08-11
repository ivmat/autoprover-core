/-
  AutoproverCorpus.Reliability.VonNeumannFaultyOrgan2

  Von Neumann multiplexing, one extra recursion level: a nine-gate organ on top of the single-
  stage faulty-organ analysis, with the error after a second restoring stage.

  Attribution: Classical (von Neumann, 1956); two-stage finite form.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Reliability.VonNeumannFaultyOrgan

namespace AutoproverCorpus.VonNeumannFaultyOrgan2

open AutoproverCorpus.VonNeumannFaultyOrgan

/-! ### The two-level (9-gate) faulty organ -/

def organError2 (e d : Rat) : Rat := organError (organError e d) d

/-! ### Part (1): the good regime — a second stage genuinely helps -/

theorem organError_at_tenth_small : organError (1 / 10) (1 / 20) = 47 / 625 := by
  rw [organError_eq]
  grind

/-- (2) The EXPLICIT witness: at the SAME small fault `d = 1/20`, a second restoring stage
    strictly reduces error further than the first alone. -/
theorem organError2_lt_organError_at_tenth_small :
    organError2 (1 / 10) (1 / 20) < organError (1 / 10) (1 / 20) := by
  unfold organError2
  rw [organError_at_tenth_small, organError_eq]
  grind

theorem two_stage_improves_at_tenth_small :
    organError2 (1 / 10) (1 / 20) < organError (1 / 10) (1 / 20) ∧
      organError (1 / 10) (1 / 20) < 1 / 10 :=
  ⟨organError2_lt_organError_at_tenth_small, organError_improves_delta_small⟩

/-! ### Part (2): the sharpness the NAME needs — at large d, a second stage does NOT help -/

theorem organError2_eq_half (e : Rat) : organError2 e (1 / 2) = 1 / 2 := by
  unfold organError2
  have h1 : organError e (1 / 2) = 1 / 2 := organError_delta_half e
  rw [h1]
  exact organError_delta_half (1 / 2)

/-- (3a) No marginal benefit from the second stage at `d = 1/2`: two stages give the same output
    error as one. -/
theorem organError2_eq_organError_at_half (e : Rat) :
    organError2 e (1 / 2) = organError e (1 / 2) := by
  rw [organError2_eq_half, organError_delta_half]

/-- (3b) Two stages together still fail to beat the raw single-wire baseline `e` at `d = 1/2`,
    for every `e ≤ 1/2` — iterating a maximally faulty organ is not unconditionally good; it does
    not even beat NOT restoring at all. -/
theorem organError2_no_improvement_at_half {e : Rat} (he : e ≤ 1 / 2) :
    organError2 e (1 / 2) ≥ e := by
  rw [organError2_eq_half]
  exact he

/-! ### Part (3): d is essential across levels — the assembled explicit witness pair -/

/-- (4) d is essential across levels: fixing `e = 1/10` and varying only `d`, a second
    restoring stage strictly helps (past the already-strict one-stage result, past the baseline)
    at `d = 1/20`, but adds zero marginal benefit and still fails to beat the baseline at
    `d = 1/2` — the verdict on whether iterating helps flips solely because of the organ's own
    fault rate, held fixed across both levels, with `e` held fixed across both regimes. This is
    the sharpness the name "iterated faulty organ" needs: iteration is not unconditionally good. -/
theorem organError2_delta_load_bearing :
    (organError2 (1 / 10) (1 / 20) < organError (1 / 10) (1 / 20) ∧
        organError (1 / 10) (1 / 20) < 1 / 10) ∧
      (organError2 (1 / 10) (1 / 2) = organError (1 / 10) (1 / 2) ∧
        organError2 (1 / 10) (1 / 2) ≥ 1 / 10) :=
  ⟨two_stage_improves_at_tenth_small,
   ⟨organError2_eq_organError_at_half (1 / 10),
    organError2_no_improvement_at_half (by grind : (1 / 10 : Rat) ≤ 1 / 2)⟩⟩

end AutoproverCorpus.VonNeumannFaultyOrgan2
