/-
  AutoproverCorpus.Distributed.AbstractQuorumSystem

  Abstract quorum systems: pairwise-intersecting quorums exclude conflicting certification, with
  majorities and Byzantine quorums as instances. Voters are modelled as casting a single
  immutable vote (no equivocation); the equivocation-aware strengthening is proved separately
  (see EquivocationAwareQuorum).

  Attribution: Classical (Malkhi and Reiter, 1998).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Distributed.QuorumIntersection
import AutoproverCorpus.Distributed.ByzantineThreshold

namespace AutoproverCorpus.AbstractQuorumSystem

variable {V : Type u}

/-! ### The abstraction -/

/-- An abstract quorum system: a predicate on lists picking out which lists are
    quorums. -/
def QuorumSystem (V : Type u) := List V → Prop

def PairwiseIntersecting (Q : QuorumSystem V) : Prop :=
  ∀ q1 q2, Q q1 → Q q2 → ∃ v, v ∈ q1 ∧ v ∈ q2

/-! ### (a) The general consistency theorem -/

/-- **Abstract quorum-system consistency.** For ANY `PairwiseIntersecting` system, two of
    its quorums that unanimously certify outcomes `A` and `B` respectively force `A = B`
    — no two quorums of a pairwise-intersecting system can ever certify contradictory
    verdicts. Proved purely from the intersection witness: the shared voter cannot have
    cast two different votes. -/
theorem quorum_system_consistent {Outcome : Type v} {Q : QuorumSystem V}
    (hpi : PairwiseIntersecting Q) {vote : V → Outcome} {q1 q2 : List V} {A B : Outcome}
    (hq1 : Q q1) (hq2 : Q q2)
    (hvoteA : ∀ v ∈ q1, vote v = A) (hvoteB : ∀ v ∈ q2, vote v = B) :
    A = B := by
  obtain ⟨v, hv1, hv2⟩ := hpi q1 q2 hq1 hq2
  rw [← hvoteA v hv1, ← hvoteB v hv2]

/-- The majority quorum system over a fixed `Nodup` universe `u`. -/
def MajorityQuorums (u : List V) : QuorumSystem V :=
  fun q => q.Nodup ∧ q ⊆ u ∧ AutoproverCorpus.QuorumIntersection.IsMajority u q

theorem majority_pairwise_intersecting {u : List V} (hu : u.Nodup) :
    PairwiseIntersecting (MajorityQuorums u) := by
  intro q1 q2 hQ1 hQ2
  obtain ⟨hq1n, hq1s, hq1m⟩ := hQ1
  obtain ⟨hq2n, hq2s, hq2m⟩ := hQ2
  exact AutoproverCorpus.QuorumIntersection.quorum_intersect hu hq1n hq2n hq1s hq2s hq1m hq2m

/-- The Byzantine `2f+1`-of-`n` quorum system over a fixed `Nodup` node set `nodes`. -/
def ByzantineQuorums (nodes : List V) (f : Nat) : QuorumSystem V :=
  fun q => q.Nodup ∧ q ⊆ nodes ∧ 2 * f + 1 ≤ q.length

theorem byzantine_pairwise_intersecting [DecidableEq V] {nodes : List V} {f : Nat}
    (hnodes : nodes.Nodup) (hn : nodes.length ≤ 3 * f + 1) :
    PairwiseIntersecting (ByzantineQuorums nodes f) := by
  intro q1 q2 hQ1 hQ2
  obtain ⟨hq1n, hq1s, hq1len⟩ := hQ1
  obtain ⟨hq2n, hq2s, hq2len⟩ := hQ2
  have hbig := AutoproverCorpus.ByzantineThreshold.byzantine_intersect_size
    hnodes hq1n hq2n hq1s hq2s hn hq1len hq2len
  have hpos : 0 < (AutoproverCorpus.ByzantineThreshold.interOf q1 q2).length := by omega
  obtain ⟨v, hv⟩ := List.exists_mem_of_length_pos hpos
  have hvmem := List.mem_filter.mp hv
  exact ⟨v, of_decide_eq_true hvmem.2, hvmem.1⟩

/-! ### (d) Instance — a system without pairwise intersection admits contradiction -/

/-- A two-quorum system with no pairwise intersection: `[1,2]` and `[3,4]` are disjoint
    quorums over a shared 4-node universe. -/
def sampleQ (q : List Nat) : Prop := q = [1, 2] ∨ q = [3, 4]

/-- A vote function separating the two quorums. -/
def sampleVote (v : Nat) : Nat := if v ≤ 2 then 0 else 1

/-- **The abstraction is not vacuous.** `sampleQ` is a genuine (non-pairwise-
    intersecting) system whose two quorums unanimously certify DIFFERENT outcomes: `[1,2]`
    all vote `0`, `[3,4]` all vote `1`, and `0 ≠ 1` — exactly the contradictory
    certification `PairwiseIntersecting` rules out. Checked concretely by `decide`. -/
example : ∃ q1 q2 : List Nat, sampleQ q1 ∧ sampleQ q2 ∧
    (∀ v ∈ q1, sampleVote v = 0) ∧ (∀ v ∈ q2, sampleVote v = 1) ∧ (0 : Nat) ≠ 1 :=
  ⟨[1, 2], [3, 4], Or.inl rfl, Or.inr rfl, by decide, by decide, by decide⟩

/-- Confirming the hypothesis fails for `sampleQ`: it is not
    `PairwiseIntersecting` — `[1,2]` and `[3,4]` share no member. This is what makes (the
    counterexample above) a genuine witness that the `PairwiseIntersecting` hypothesis is
    essential, not a system that happens to also satisfy it. -/
theorem sampleQ_not_pairwise_intersecting : ¬ PairwiseIntersecting sampleQ := by
  intro h
  obtain ⟨v, hv1, hv2⟩ := h [1, 2] [3, 4] (Or.inl rfl) (Or.inr rfl)
  rcases List.mem_cons.mp hv1 with h1 | h1
  · rcases List.mem_cons.mp hv2 with h2 | h2
    · omega
    · rcases List.mem_cons.mp h2 with h2 | h2
      · omega
      · exact absurd h2 (List.not_mem_nil)
  · rcases List.mem_cons.mp h1 with h1 | h1
    · rcases List.mem_cons.mp hv2 with h2 | h2
      · omega
      · rcases List.mem_cons.mp h2 with h2 | h2
        · omega
        · exact absurd h2 (List.not_mem_nil)
    · exact absurd h1 (List.not_mem_nil)

end AutoproverCorpus.AbstractQuorumSystem
