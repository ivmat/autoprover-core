/-
  AutoproverCorpus.Probability.CovZeroNotIndep

  Zero covariance does not imply independence: an explicit finite counterexample over the
  rationals, closed by `decide`.

  Attribution: Classical counterexample (standard probability folklore).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.CovZeroNotIndep

/-- The finite sample space: `X` uniform on `{-1, 0, 1}`, `Y = X ^ 2`, each outcome carrying
    an explicit rational weight `1/3` (built via `mkRat`, see file-header deviation note).
    Each entry is `(x, y, weight)`. -/
def sample : List (Rat × Rat × Rat) :=
  [(-1, 1, mkRat 1 3), (0, 0, mkRat 1 3), (1, 1, mkRat 1 3)]

/-- The three weights sum to `1` — this IS a probability distribution. -/
theorem weights_sum_to_one :
    sample.foldr (fun t acc => t.2.2 + acc) (0 : Rat) = 1 := by
  simp only [sample, List.foldr, Rat.add_def']
  decide

/-- Expectation of an arbitrary function `f` of `(x, y)`, as a finite weighted sum over the
    sample space. -/
def E (f : Rat → Rat → Rat) : Rat :=
  sample.foldr (fun t acc => t.2.2 * f t.1 t.2.1 + acc) 0

def EX : Rat := E (fun x _ => x)
def EY : Rat := E (fun _ y => y)
def EXY : Rat := E (fun x y => x * y)

/-- Covariance, defined exactly as `Cov(X, Y) = E[XY] - E[X]E[Y]`. -/
def Cov : Rat := EXY - EX * EY

/-- Joint probability `P(X = a ∧ Y = b)`, as a finite weighted sum over the sample space. -/
def PJoint (a b : Rat) : Rat :=
  sample.foldr (fun t acc => (if t.1 = a ∧ t.2.1 = b then t.2.2 else 0) + acc) 0

/-- Marginal probability `P(X = a)`. -/
def PX (a : Rat) : Rat :=
  sample.foldr (fun t acc => (if t.1 = a then t.2.2 else 0) + acc) 0

/-- Marginal probability `P(Y = b)`. -/
def PY (b : Rat) : Rat :=
  sample.foldr (fun t acc => (if t.2.1 = b then t.2.2 else 0) + acc) 0

/-- (1) The zero-covariance half of the counterexample: `Cov(X, Y) = 0`. -/
theorem cov_eq_zero : Cov = 0 := by
  simp only [Cov, EXY, EX, EY, E, sample, List.foldr, Rat.add_def', Rat.mul_def', Rat.sub_def']
  decide

/-- The concrete witness pair exhibiting dependence: `X = -1` forces `Y = 1`, so the joint
    probability `P(X = -1 ∧ Y = 1) = 1/3` is NOT the product of the marginals
    `P(X = -1) = 1/3` and `P(Y = 1) = 2/3`. -/
theorem not_independent_witness : PJoint (-1) 1 ≠ PX (-1) * PY 1 := by
  simp only [PJoint, PX, PY, sample, List.foldr, Rat.add_def', Rat.mul_def']
  decide

theorem exists_dependent_pair : ∃ a b : Rat, PJoint a b ≠ PX a * PY b :=
  ⟨-1, 1, not_independent_witness⟩

/-- The full counterexample, packaged: `Cov(X, Y) = 0` yet `X` and `Y` are not independent.
    This refutes the TRAP-3 claim "`Cov(X, Y) = 0 ⟹ X ⟂ Y`" outright — zero covariance does
    NOT imply independence. -/
theorem cov_zero_not_indep :
    Cov = 0 ∧ ∃ a b : Rat, PJoint a b ≠ PX a * PY b :=
  ⟨cov_eq_zero, exists_dependent_pair⟩

end AutoproverCorpus.CovZeroNotIndep
