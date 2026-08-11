/-
  AutoproverCorpus.Reliability.VonNeumannFaultyOrgan

  Von Neumann multiplexing with a FAULTY restoring organ: the restoring stage itself is built
  from unreliable components, and the error analysis accounts for its failures. Scoped to an
  explicit error function with an organ-failure parameter that is essential to the analysis;
  the full symbolic threshold is not claimed.

  Attribution: Classical (von Neumann, 1956); scoped finite form.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Reliability.TripleModularRedundancy

namespace AutoproverCorpus.VonNeumannFaultyOrgan

/-! ### Part (1): XOR-composition of two independent Bernoulli events -/

/-- Boolean XOR, defined locally (not relying on any core primitive by an unclear name):
    `bxor a b = true` iff exactly one of `a`, `b` is `true`. -/
def bxor (a b : Bool) : Bool := (a && !b) || (!a && b)

/-- The 4 outcomes of two independent binary events: `t.1` = "the ideal (perfect) majority
    output is wrong", `t.2` = "the restoring organ's own gate misfires on this instance". -/
def xorOutcomes : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

/-- Weight of one joint outcome under independence: `m` is the probability the ideal majority
    is wrong, `d` is the probability the gate itself misfires. -/
def xorWeight (m d : Rat) (t : Bool × Bool) : Rat :=
  (if t.1 then m else 1 - m) * (if t.2 then d else 1 - d)

/-- Total probability the FAULTY organ's actual output is wrong: a misfiring gate
    (`t.2 = true`) flips the ideal majority output, so the actual output is wrong exactly when
    ideal-wrong XOR gate-misfires holds. -/
def xorErrorProb (m d : Rat) : Rat :=
  (xorOutcomes.filter (fun t => bxor t.1 t.2)).foldr (fun t acc => xorWeight m d t + acc) 0

/-- The concrete filtering step: of the 4 joint outcomes, exactly the 2 where the events
    DISAGREE survive (ideal-wrong-only, gate-misfires-only) -- the XOR truth table, closed by
    `decide`. -/
theorem filtered_xor_outcomes :
    xorOutcomes.filter (fun t => bxor t.1 t.2) = [(false, true), (true, false)] := by
  decide

theorem xorErrorProb_eq (m d : Rat) : xorErrorProb m d = (1 - d) * m + d * (1 - m) := by
  unfold xorErrorProb
  rw [filtered_xor_outcomes]
  simp only [xorWeight, List.foldr]
  grind

/-! ### Part (2): the faulty 3-input restoring organ -/

def organError (e d : Rat) : Rat :=
  xorErrorProb (AutoproverCorpus.TripleModularRedundancy.errorProb3 e) d

theorem organError_eq (e d : Rat) :
    organError e d = (1 - d) * (3 * e ^ 2 - 2 * e ^ 3) + d * (1 - (3 * e ^ 2 - 2 * e ^ 3)) := by
  unfold organError
  rw [AutoproverCorpus.TripleModularRedundancy.majority3_error_poly]
  exact xorErrorProb_eq _ d

theorem organError_delta_zero (e : Rat) : organError e 0 = 3 * e ^ 2 - 2 * e ^ 3 := by
  rw [organError_eq]
  grind

/-- (4) ANTI-CONTRACTION, general: at `d = 1/2` (a maximally faulty gate -- a coin flip) the
    organ's output error is EXACTLY `1/2` for EVERY input error `e`, independent of how
    reliable the input wires are -- a 50%-misfire gate is information-destroying. -/
theorem organError_delta_half (e : Rat) : organError e (1 / 2) = 1 / 2 := by
  rw [organError_eq]
  grind

theorem organError_delta_half_no_improvement {e : Rat} (he : e ≤ 1 / 2) :
    organError e (1 / 2) ≥ e := by
  rw [organError_delta_half]
  exact he

/-! ### Part (3): d is essential -- witnesses at a fixed input error -/

theorem organError_improves_delta_zero :
    organError (1 / 10) 0 < 1 / 10 := by
  rw [organError_delta_zero]
  exact AutoproverCorpus.TripleModularRedundancy.threshold_strict_at_tenth

/-- (5b) At the same `e = 1/10`, a nonzero but small fault (`d = 1/20`) still
    improves reliability -- the effect of items (3)/(4) is not a `d = 0` artifact. -/
theorem organError_improves_delta_small :
    organError (1 / 10) (1 / 20) < 1 / 10 := by
  rw [organError_eq]
  grind

/-- (5c) At the same `e = 1/10`, a large fault (`d = 1/2`) does not improve reliability --
    from the general anti-contraction fact (4'). -/
theorem organError_no_improvement_delta_half :
    organError (1 / 10) (1 / 2) ≥ 1 / 10 := by
  apply organError_delta_half_no_improvement
  grind

theorem delta_load_bearing :
    (organError (1 / 10) 0 < 1 / 10) ∧
    (organError (1 / 10) (1 / 20) < 1 / 10) ∧
    (organError (1 / 10) (1 / 2) ≥ 1 / 10) :=
  ⟨organError_improves_delta_zero, organError_improves_delta_small,
   organError_no_improvement_delta_half⟩

end AutoproverCorpus.VonNeumannFaultyOrgan
