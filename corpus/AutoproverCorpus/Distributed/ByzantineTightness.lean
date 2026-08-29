/-
  AutoproverCorpus.Distributed.ByzantineTightness

  Tightness of the Byzantine threshold: at n = 3f, two size-2f quorums certify contradictory
  outcomes - a static configuration exhibiting two uniform but contradictory certified views,
  not a reachability result (no transition system is modeled here). This makes 3f+1 nodes
  necessary, not just
  sufficient, ONLY GIVEN the unformalized liveness premise that a usable quorum must be
  attainable while up to f nodes are silent — i.e. quorum size ≤ n − f; the module itself
  proves that the LARGER 2f+1-sized quorums remain safe at n = 3f.

  Attribution: Classical (Pease, Shostak and Lamport, 1980).

  SCOPE NOTE. The tightness half is a single concrete counterexample: f = 1 and n = 3, with the
  node universe `[1, 2, 3]`, two size-2 (not size-2f+1) quorums, and the shared node faulty.
  There is no construction of a disagreeing instance for general f, so "3f+1 is necessary" is
  witnessed at f = 1 only, and even that witness only bears on necessity under the liveness
  premise above (quorum size ≤ n − f), which is neither formalized nor proved by this module.
  Part (1) of the module (`still_correct_at_n_eq_3f_fixed_quorum`) IS general in f, but it is the
  positive direction, not the tightness claim, and it proves that 2f+1-sized quorums stay SAFE
  at n = 3f — so the size-2f witness does not by itself force 3f+1.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Distributed.ByzantineThreshold

namespace AutoproverCorpus.ByzantineTightness

open AutoproverCorpus.ByzantineThreshold

/-! ### (1) The naive attempt does not break — documented, not swept under -/

theorem still_correct_at_n_eq_3f_fixed_quorum {V : Type u} [DecidableEq V]
    {nodes q1 q2 faulty : List V} {f : Nat}
    (hnodes : nodes.Nodup) (hq1 : q1.Nodup) (hq2 : q2.Nodup)
    (hsub1 : q1 ⊆ nodes) (hsub2 : q2 ⊆ nodes)
    (hn : nodes.length = 3 * f)
    (hq1len : 2 * f + 1 ≤ q1.length) (hq2len : 2 * f + 1 ≤ q2.length)
    (hfaultylen : faulty.length ≤ f) :
    ∃ v, v ∈ q1 ∧ v ∈ q2 ∧ v ∉ faulty :=
  byzantine_correct_witness hnodes hq1 hq2 hsub1 hsub2 (by omega) hq1len hq2len hfaultylen

/-! ### (2) Counterexample separating the hypotheses — the tight-converse instance -/

/-- The `n = 3` node universe (`f = 1`, so `n = 3f`). -/
def wNodes : List Nat := [1, 2, 3]

def wQ1 : List Nat := [1, 2]

/-- A second size-`2` quorum, overlapping `wQ1` only at node `2`. -/
def wQ2 : List Nat := [2, 3]

/-- The fault set: exactly the shared node, size `1 = f`. -/
def wFaulty : List Nat := [2]

example : wNodes.Nodup := by decide
example : wQ1.Nodup := by decide
example : wQ2.Nodup := by decide
example : wQ1 ⊆ wNodes := by decide
example : wQ2 ⊆ wNodes := by decide
example : wNodes.length = 3 * 1 := by decide
example : wFaulty.length ≤ 1 := by decide

example : interOf wQ1 wQ2 = wFaulty := by decide

/-- **No correct shared node** — the direct negation of what
    `byzantine_correct_witness` would conclude if its (unmet, here) `2f+1`
    quorum-size hypothesis held. -/
theorem no_correct_witness_at_wQ1_wQ2 : ¬ ∃ v, v ∈ wQ1 ∧ v ∈ wQ2 ∧ v ∉ wFaulty := by
  decide

/-- What quorum `wQ1` hears from each node. -/
def wVote1 (v : Nat) : Nat := if v ≤ 2 then 0 else 99

def wVote2 (v : Nat) : Nat := if v ≥ 2 then 1 else 99

example : ∀ v ∈ wQ1, wVote1 v = 0 := by decide
example : ∀ v ∈ wQ2, wVote2 v = 1 := by decide

/-- **The equivocation witness.** The faulty node `2` reports `0` to `wQ1`'s
    view and `1` to `wQ2`'s view — different values, not merely two
    unrelated functions that happen to disagree elsewhere. -/
example : wVote1 2 ≠ wVote2 2 := by decide

theorem main_theorem :
    wNodes.Nodup ∧ wQ1.Nodup ∧ wQ2.Nodup ∧
    wQ1 ⊆ wNodes ∧ wQ2 ⊆ wNodes ∧
    wNodes.length = 3 * 1 ∧
    wFaulty.length ≤ 1 ∧
    interOf wQ1 wQ2 = wFaulty ∧
    (¬ ∃ v, v ∈ wQ1 ∧ v ∈ wQ2 ∧ v ∉ wFaulty) ∧
    (∀ v ∈ wQ1, wVote1 v = 0) ∧
    (∀ v ∈ wQ2, wVote2 v = 1) ∧
    (0 : Nat) ≠ 1 ∧
    wVote1 2 ≠ wVote2 2 := by
  decide

end AutoproverCorpus.ByzantineTightness
