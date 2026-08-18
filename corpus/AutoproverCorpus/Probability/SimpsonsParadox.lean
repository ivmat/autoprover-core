/-
  AutoproverCorpus.Probability.SimpsonsParadox

  Simpson's paradox: a success rate that dominates within EVERY stratum can be dominated once
  the strata are pooled. Two results are proved here.

  (1) The counterexample (`simpsons_paradox`), on the classical kidney-stone treatment table:
      treatment A beats treatment B on small stones (81/87 vs 234/270) and on large stones
      (192/263 vs 55/80), yet loses on the pooled totals (273/350 vs 289/350). Rates are
      compared exactly, by cross-multiplication over `Nat` — `a/n > b/m` is stated as
      `b * n < a * m` — so no rounding, division, or `Rat` arithmetic enters the claim.

  (2) The condition under which the reversal is impossible (`no_paradox_under_equal_allocation`):
      if the two treatments allocate their subjects across the strata in the same RATIO
      (`n1 * m2 = m1 * n2`), then stratum-wise dominance does carry to the pooled table. The
      paradox is therefore a fact about UNEQUAL allocation (confounding), not an inconsistency
      in the arithmetic — this is the classical collapsibility condition, and it is proved in
      general form for arbitrary counts, not just for the table above.

  Attribution: E. H. Simpson, "The Interpretation of Interaction in Contingency Tables", 1951;
  the phenomenon was noted earlier by G. U. Yule (1903) and K. Pearson (1899). The numeric
  instance is the kidney-stone treatment table of Charig, Webb, Payne and Wickham (1986), as
  popularized by Julious and Mullee (1994).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.SimpsonsParadox

/-! ### Comparing rates exactly, without division -/

/-- `Better a n b m` says the success rate `a/n` strictly exceeds `b/m`, stated by
    cross-multiplication so that it is an exact `Nat` fact: `b * n < a * m`. For positive
    denominators this is equivalent to the rate comparison, and it avoids division entirely. -/
abbrev Better (a n b m : Nat) : Prop := b * n < a * m

/-! ### (1) The counterexample: the kidney-stone table -/

/-- Treatment A (open surgery), small stones: 81 successes out of 87. -/
abbrev aSmall : Nat := 81
abbrev nSmall : Nat := 87

/-- Treatment B (percutaneous nephrolithotomy), small stones: 234 out of 270. -/
abbrev bSmall : Nat := 234
abbrev mSmall : Nat := 270

/-- Treatment A, large stones: 192 out of 263. -/
abbrev aLarge : Nat := 192
abbrev nLarge : Nat := 263

/-- Treatment B, large stones: 55 out of 80. -/
abbrev bLarge : Nat := 55
abbrev mLarge : Nat := 80

/-- **A wins on small stones**: `81/87 ≈ 0.931 > 0.867 ≈ 234/270`, exactly
    `234 * 87 = 20358 < 21870 = 81 * 270`. -/
theorem a_better_small : Better aSmall nSmall bSmall mSmall := by decide

/-- **A wins on large stones**: `192/263 ≈ 0.730 > 0.688 ≈ 55/80`, exactly
    `55 * 263 = 14465 < 15360 = 192 * 80`. -/
theorem a_better_large : Better aLarge nLarge bLarge mLarge := by decide

/-- **B wins on the pooled table**: `273/350 = 0.78 < 0.826 ≈ 289/350`. Both treatments treated
    350 subjects in total, so the pooled comparison is just `273 < 289`. -/
theorem b_better_pooled :
    Better (bSmall + bLarge) (mSmall + mLarge) (aSmall + aLarge) (nSmall + nLarge) := by decide

/-- The pooled totals, spelled out: 273 of 350 for A, 289 of 350 for B. -/
theorem pooled_totals :
    aSmall + aLarge = 273 ∧ nSmall + nLarge = 350 ∧
      bSmall + bLarge = 289 ∧ mSmall + mLarge = 350 := by decide

/-- **Simpson's paradox, packaged.** Treatment A dominates treatment B in every stratum and is
    dominated by it after pooling. In particular stratum-wise dominance does NOT imply pooled
    dominance: reporting only the pooled table reverses the conclusion. -/
theorem simpsons_paradox :
    Better aSmall nSmall bSmall mSmall ∧
    Better aLarge nLarge bLarge mLarge ∧
    ¬ Better (aSmall + aLarge) (nSmall + nLarge) (bSmall + bLarge) (mSmall + mLarge) := by
  exact ⟨a_better_small, a_better_large, by decide⟩

/-- The unequal allocation that drives the reversal: treatment A took the large-stone stratum
    (the harder cases) 263 times out of 350, treatment B only 80 times out of 350. The
    allocation ratios differ — `87 * 80 = 6960 ≠ 71010 = 270 * 263` — which is exactly the
    hypothesis of the theorem below, and it fails here. -/
theorem allocation_is_unequal : nSmall * mLarge ≠ mSmall * nLarge := by decide

/-! ### (2) Equal allocation ratios rule the paradox out -/

/-- **Collapsibility under equal allocation.** If the two groups split across the two strata in
    the same ratio (`n1 * m2 = m1 * n2`) and both strata are nonempty for the relevant group,
    then stratum-wise dominance carries to the pooled table: no Simpson reversal is possible.

    The proof turns the allocation identity into the two cross-stratum inequalities
    `b1 * n2 < a1 * m2` and `b2 * n1 < a2 * m1` (by multiplying each stratum's inequality by the
    other stratum's size and cancelling), which are precisely the two extra terms the pooled
    products contribute beyond the given ones. Adding the four strict inequalities gives the
    pooled comparison.

    This is the honest reading of the counterexample above: the paradox is a fact about unequal
    allocation (confounding), not a defect of the rate comparison. -/
theorem no_paradox_under_equal_allocation
    {a1 n1 b1 m1 a2 n2 b2 m2 : Nat}
    (hm1 : 0 < m1) (hn2 : 0 < n2)
    (halloc : n1 * m2 = m1 * n2)
    (h1 : Better a1 n1 b1 m1) (h2 : Better a2 n2 b2 m2) :
    Better (a1 + a2) (n1 + n2) (b1 + b2) (m1 + m2) := by
  unfold Better at h1 h2 ⊢
  -- The allocation identity forces the other two sizes to be positive as well.
  have hprod : 0 < n1 * m2 := by rw [halloc]; exact Nat.mul_pos hm1 hn2
  have hn1 : 0 < n1 := Nat.pos_of_ne_zero (fun h => by simp [h] at hprod)
  have hm2 : 0 < m2 := Nat.pos_of_ne_zero (fun h => by simp [h] at hprod)
  -- Cross-stratum inequality 1: multiply `h1` by `m2` and cancel `m1`.
  have k1 : b1 * n2 < a1 * m2 := by
    have hstep : (b1 * n1) * m2 < (a1 * m1) * m2 := (Nat.mul_lt_mul_right hm2).mpr h1
    have hl : (b1 * n1) * m2 = (b1 * n2) * m1 := by
      calc (b1 * n1) * m2 = b1 * (n1 * m2) := by ac_rfl
        _ = b1 * (m1 * n2) := by rw [halloc]
        _ = (b1 * n2) * m1 := by ac_rfl
    have hr : (a1 * m1) * m2 = (a1 * m2) * m1 := by ac_rfl
    rw [hl, hr] at hstep
    exact (Nat.mul_lt_mul_right hm1).mp hstep
  -- Cross-stratum inequality 2: multiply `h2` by `n1` and cancel `n2`.
  have k2 : b2 * n1 < a2 * m1 := by
    have hstep : (b2 * n2) * n1 < (a2 * m2) * n1 := (Nat.mul_lt_mul_right hn1).mpr h2
    have hl : (b2 * n2) * n1 = (b2 * n1) * n2 := by ac_rfl
    have hr : (a2 * m2) * n1 = (a2 * m1) * n2 := by
      calc (a2 * m2) * n1 = a2 * (n1 * m2) := by ac_rfl
        _ = a2 * (m1 * n2) := by rw [halloc]
        _ = (a2 * m1) * n2 := by ac_rfl
    rw [hl, hr] at hstep
    exact (Nat.mul_lt_mul_right hn2).mp hstep
  -- Expand both pooled products and add the four strict inequalities.
  have hL : (b1 + b2) * (n1 + n2) = b1 * n1 + b1 * n2 + b2 * n1 + b2 * n2 := by
    simp [Nat.add_mul, Nat.mul_add]; ac_rfl
  have hR : (a1 + a2) * (m1 + m2) = a1 * m1 + a1 * m2 + a2 * m1 + a2 * m2 := by
    simp [Nat.add_mul, Nat.mul_add]; ac_rfl
  rw [hL, hR]
  omega

/-- **Non-vacuity of the positive theorem.** A concrete equally-allocated pair: both treatments
    take 10 small-stone and 20 large-stone cases, A winning each stratum (9/10 vs 8/10 and
    12/20 vs 10/20). The theorem then delivers the pooled dominance (21/30 vs 18/30) — so the
    hypothesis is satisfiable and the conclusion is a genuine consequence, not vacuous. -/
example : Better (9 + 12) (10 + 20) (8 + 10) (10 + 20) :=
  no_paradox_under_equal_allocation (a1 := 9) (n1 := 10) (b1 := 8) (m1 := 10)
    (a2 := 12) (n2 := 20) (b2 := 10) (m2 := 20)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end AutoproverCorpus.SimpsonsParadox
