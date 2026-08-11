/-
  AutoproverCorpus.Reliability.TripleModularRedundancy

  Triple modular redundancy with a PERFECT majority voter, over the rationals: three independent
  components each failing with probability e, majority-voted, fail with probability 3e^2 - 2e^3,
  which improves on e exactly when 0 < e < 1/2 (with sharpness at e = 1/2). NOTE: this is the
  perfect-voter analysis only. Von Neumann's 1956 multiplexing theorem concerns a FAULTY
  restoring organ and is treated separately (see VonNeumannFaultyOrgan).

  Attribution: Classical reliability analysis (TMR with a perfect voter; cf. von Neumann, 1956,
  for the faulty-organ theorem, which this file does NOT prove).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.TripleModularRedundancy

/-! ### Part (1): the enumeration identity -/

def majority3 (b1 b2 b3 : Bool) : Bool :=
  (b1 && b2) || (b2 && b3) || (b1 && b3)

/-- The 8 outcomes of three independent per-gate error indicators; `bi = true` means gate `i`
    is wrong on this outcome. -/
def outcomes3 : List (Bool × Bool × Bool) :=
  [(false, false, false), (false, false, true), (false, true, false), (false, true, true),
   (true, false, false), (true, false, true), (true, true, false), (true, true, true)]

/-- Probability weight of one outcome given per-gate error probability `ε`: `ε` for each wrong
    gate, `1 − ε` for each right gate, multiplied together (independence). -/
def weight3 (e : Rat) (t : Bool × Bool × Bool) : Rat :=
  (if t.1 then e else 1 - e) * (if t.2.1 then e else 1 - e) * (if t.2.2 then e else 1 - e)

/-- Total probability of a wrong majority vote: the sum of outcome weights over exactly the
    outcomes where `majority3` reports `true` (2-or-3 gates wrong). -/
def errorProb3 (e : Rat) : Rat :=
  (outcomes3.filter (fun t => majority3 t.1 t.2.1 t.2.2)).foldr (fun t acc => weight3 e t + acc) 0

/-- The concrete filtering step: of the 8 outcomes, exactly the 4 with ≥ 2 wrong gates survive
    (the three "exactly 2 wrong" permutations, plus "all 3 wrong"). Pure `Bool` computation on
    a concrete list, closed by `decide`. -/
theorem filtered_outcomes :
    outcomes3.filter (fun t => majority3 t.1 t.2.1 t.2.2) =
      [(false, true, true), (true, false, true), (true, true, false), (true, true, true)] := by
  decide

/-- (1) The enumeration identity: independent per-gate error `ε` gives majority-wrong
    probability exactly `3ε² − 2ε³` (`= 3ε²(1−ε) + ε³`, the "≥ 2 of 3 wrong" closed form),
    proved by enumerating the 8 outcomes, filtering to the 4 majority-wrong ones, and closing
    the resulting concrete polynomial identity with `grind`'s `Rat` ring normalizer. -/
theorem majority3_error_poly (e : Rat) : errorProb3 e = 3 * e ^ 2 - 2 * e ^ 3 := by
  unfold errorProb3
  rw [filtered_outcomes]
  simp only [weight3, List.foldr]
  grind

/-! ### Part (2): the improvement threshold -/

/-- Mini-lemma: a nonnegative times a nonpositive `Rat` is `≤ 0`. Core Lean's `Rat` has no
    `OrderedRing`/`LinearOrder` combinator bundling this (only the raw pieces), and `grind`
    does not close it automatically (tested, confirmed to fail — it needs a genuine
    nonlinear-sign case split `grind`'s linear engine doesn't attempt on its own), so it is
    hand-proved from `Rat.mul_le_mul_of_nonneg_left` (`c*a ≤ c*b` for `a ≤ b`, `0 ≤ c`),
    instantiated at `a = y, b = 0, c = x`. -/
theorem mul_nonneg_nonpos {x y : Rat} (hx : 0 ≤ x) (hy : y ≤ 0) : x * y ≤ 0 := by
  have h := Rat.mul_le_mul_of_nonneg_left hy hx
  simpa using h

/-- (2) The improvement threshold: for `ε ∈ [0, 1]`, the 3-way majority error `3ε² − 2ε³` is
    strictly below the per-gate error `ε` exactly when `0 < ε < 1/2` — i.e. majority-voting
    strictly improves reliability exactly below the classical `1/2` threshold. Route: factor
    `ε − (3ε² − 2ε³) = ε(1−ε)(1−2ε)` (`grind`, plain ring identity), then hand-chase the sign
    of each of the three linear factors (see file header for why `grind` alone does not close
    the sign analysis directly). -/
theorem improvement_iff {e : Rat} (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    3 * e ^ 2 - 2 * e ^ 3 < e ↔ (0 < e ∧ e < 1 / 2) := by
  have hfact : e - (3 * e ^ 2 - 2 * e ^ 3) = e * (1 - e) * (1 - 2 * e) := by grind
  constructor
  · intro hlt
    have hposdiff : (0:Rat) < e - (3 * e ^ 2 - 2 * e ^ 3) := (Rat.lt_iff_sub_pos _ _).mp hlt
    rw [hfact] at hposdiff
    constructor
    · -- 0 < e: if e = 0 the product collapses to 0, contradicting strict positivity.
      have hnot : ¬ (e ≤ 0) := by
        intro hle
        have heq : e = 0 := Rat.le_antisymm hle h0
        rw [heq] at hposdiff
        grind
      exact Rat.not_le.mp hnot
    · -- e < 1/2: if 1/2 ≤ e, then e(1−e) ≥ 0 (both factors nonneg on [0,1]) while
      -- 1 − 2e ≤ 0, so the whole product is ≤ 0, contradicting strict positivity.
      have hnot : ¬ ((1:Rat) / 2 ≤ e) := by
        intro hge
        have h1e : (0:Rat) ≤ 1 - e := by
          have := (Rat.le_iff_sub_nonneg e 1).mp h1
          simpa using this
        have hprodnn : (0:Rat) ≤ e * (1 - e) := Rat.mul_nonneg h0 h1e
        have hz : 1 - 2 * e ≤ 0 := by grind
        have hcontra : e * (1 - e) * (1 - 2 * e) ≤ 0 := mul_nonneg_nonpos hprodnn hz
        exact (Rat.not_le.mpr hposdiff) hcontra
      exact Rat.not_le.mp hnot
  · intro ⟨he0, heh⟩
    -- 0 < e < 1/2 gives all three factors e, 1−e, 1−2e strictly positive, so their product is.
    have he1 : e < 1 := by grind
    have h1me : (0:Rat) < 1 - e := (Rat.lt_iff_sub_pos _ _).mp he1
    have h12e : (0:Rat) < 1 - 2 * e := by grind
    have hpos : (0:Rat) < e * (1 - e) * (1 - 2 * e) :=
      Rat.mul_pos (Rat.mul_pos he0 h1me) h12e
    have hposdiff : (0:Rat) < e - (3 * e ^ 2 - 2 * e ^ 3) := by rw [hfact]; exact hpos
    exact (Rat.lt_iff_sub_pos _ _).mpr hposdiff

/-! ### Part (3): the threshold is sharp -/

/-- (3a) At exactly `ε = 1/2` the majority error EQUALS the per-gate error (no improvement,
    no degradation) — the threshold is sharp, not merely approached. Closed directly by
    `grind`'s `Rat` ring normalizer after substituting `ε = 1/2`. -/
theorem threshold_eq_at_half : (3:Rat) * (1/2:Rat) ^ 2 - 2 * (1/2:Rat) ^ 3 = 1 / 2 := by grind

/-- (3b) A concrete strict-improvement witness below the threshold: at `ε = 1/10`,
    `3ε² − 2ε³ = 0.028 < 0.1 = ε`. Closed directly by `grind`'s `Rat` ring/order engine on
    fully concrete rationals (no `mkRat`/`decide` detour needed here — this is the case where
    `grind`'s linear engine suffices, unlike the general symbolic sign analysis in Part (2)). -/
theorem threshold_strict_at_tenth :
    (3:Rat) * (1/10:Rat) ^ 2 - 2 * (1/10:Rat) ^ 3 < 1 / 10 := by grind

/-- The assembled sharpness statement: equality exactly at the threshold, and a concrete
    strict-improvement instance strictly below it. -/
theorem threshold_sharp :
    ((3:Rat) * (1/2:Rat) ^ 2 - 2 * (1/2:Rat) ^ 3 = 1 / 2) ∧
      ((3:Rat) * (1/10:Rat) ^ 2 - 2 * (1/10:Rat) ^ 3 < 1 / 10) :=
  ⟨threshold_eq_at_half, threshold_strict_at_tenth⟩

end AutoproverCorpus.TripleModularRedundancy
