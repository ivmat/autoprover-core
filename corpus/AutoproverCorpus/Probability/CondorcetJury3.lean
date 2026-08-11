/-
  AutoproverCorpus.Probability.CondorcetJury3

  Condorcet's jury theorem at fixed size three, over the rationals: a majority of three
  independent better-than-chance voters is more reliable than a single voter.

  Attribution: Classical (Condorcet, 1785); fixed-size finite case.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Reliability.TripleModularRedundancy

namespace AutoproverCorpus.CondorcetJury3

def majorityCorrect3 (p : Rat) : Rat := 1 - AutoproverCorpus.TripleModularRedundancy.errorProb3 (1 - p)

theorem majorityCorrect3_eq (p : Rat) :
    majorityCorrect3 p = 1 - (3 * (1 - p) ^ 2 - 2 * (1 - p) ^ 3) := by
  unfold majorityCorrect3
  rw [AutoproverCorpus.TripleModularRedundancy.majority3_error_poly]

theorem condorcet_jury_gain {p : Rat} (hp2 : 1 / 2 < p) (hp1 : p < 1) :
    p < majorityCorrect3 p := by
  have he0 : (0 : Rat) ≤ 1 - p := by grind
  have he1 : (1 - p : Rat) ≤ 1 := by grind
  have hepos : (0 : Rat) < 1 - p := by grind
  have hehalf : (1 - p : Rat) < 1 / 2 := by grind
  have hiff := AutoproverCorpus.TripleModularRedundancy.improvement_iff (e := 1 - p) he0 he1
  have hlt : 3 * (1 - p) ^ 2 - 2 * (1 - p) ^ 3 < 1 - p := hiff.mpr ⟨hepos, hehalf⟩
  have herr : AutoproverCorpus.TripleModularRedundancy.errorProb3 (1 - p) < 1 - p := by
    rw [AutoproverCorpus.TripleModularRedundancy.majority3_error_poly]; exact hlt
  unfold majorityCorrect3
  grind

theorem condorcet_no_gain_at_half : majorityCorrect3 (1 / 2 : Rat) = 1 / 2 := by
  have h1 : (1 - (1 / 2 : Rat)) = 1 / 2 := by grind
  rw [majorityCorrect3_eq, h1]
  grind

/-- (4) Sharpness, failure face — a concrete counterexample separating the hypotheses
    (a concrete value of `p` is what "sharp" means here): at
    `p = 1/10` (each voter correct only 1-in-10, well below chance), the majority's correctness
    is `7/250 = 0.028`, strictly less than the single voter's own correctness `1/10 = 25/250` —
    a jury of bad voters is majority-correct less often than any one of them alone. This pins
    down that `condorcet_jury_gain`'s `p > 1/2` hypothesis is essential: the inequality
    reverses below the threshold, it does not merely stop holding. -/
theorem condorcet_worse_below_half : majorityCorrect3 (1 / 10 : Rat) < 1 / 10 := by
  rw [majorityCorrect3_eq]
  grind

end AutoproverCorpus.CondorcetJury3
