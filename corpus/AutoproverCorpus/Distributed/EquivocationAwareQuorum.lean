/-
  AutoproverCorpus.Distributed.EquivocationAwareQuorum

  Equivocation-aware quorum certification: with signed voter-outcome records, faulty voters
  permitted to equivocate, correct voters casting one vote, at most f faulty voters and quorum
  intersection exceeding f, no two quorums certify conflicting outcomes.

  Attribution: Classical (Byzantine quorum systems; Malkhi and Reiter, 1998).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Distributed.ByzantineThreshold

namespace AutoproverCorpus.EquivocationAwareQuorum

variable {V : Type} [DecidableEq V] {Outcome : Type}

abbrev VoteLog (V Outcome : Type) := List (V × Outcome)

/-- Quorum `q` unanimously certifies outcome `A` in `votes`: every member of `q` has a
    matching vote record. -/
def Certifies (votes : VoteLog V Outcome) (q : List V) (A : Outcome) : Prop :=
  ∀ v ∈ q, (v, A) ∈ votes

/-- **No equivocation by correct voters.** Any two records in `votes` naming the SAME
    non-faulty voter agree on the outcome — the operative content of "at most one outcome
    per correct voter" (see header). -/
def NoEquivocation (votes : VoteLog V Outcome) (faulty : List V) : Prop :=
  ∀ r1 ∈ votes, ∀ r2 ∈ votes, r1.1 = r2.1 → r1.1 ∉ faulty → r1.2 = r2.2

def IsQuorum (nodes : List V) (f : Nat) (q : List V) : Prop :=
  q.Nodup ∧ q ⊆ nodes ∧ 2 * f + 1 ≤ q.length

/-! ### (a) The equivocation-aware consistency theorem -/

theorem equivocation_aware_consistent {nodes q1 q2 faulty : List V} {f : Nat}
    {votes : VoteLog V Outcome} {A B : Outcome}
    (hnodes : nodes.Nodup) (hn : nodes.length ≤ 3 * f + 1)
    (hq1 : IsQuorum nodes f q1) (hq2 : IsQuorum nodes f q2)
    (hfaultylen : faulty.length ≤ f)
    (hhonest : NoEquivocation votes faulty)
    (hcertA : Certifies votes q1 A) (hcertB : Certifies votes q2 B) :
    A = B := by
  obtain ⟨hq1n, hq1s, hq1len⟩ := hq1
  obtain ⟨hq2n, hq2s, hq2len⟩ := hq2
  obtain ⟨v, hv1, hv2, hvnf⟩ := AutoproverCorpus.ByzantineThreshold.byzantine_correct_witness
    hnodes hq1n hq2n hq1s hq2s hn hq1len hq2len hfaultylen
  exact hhonest (v, A) (hcertA v hv1) (v, B) (hcertB v hv2) rfl hvnf

/-! ### (b) Necessity — without the honesty hypothesis, consistency genuinely fails -/

/-- The canonical `n = 4, f = 1` universe. -/
def negNodes : List Nat := [1, 2, 3, 4]

/-- A size-3 (`2f+1`) quorum. -/
def negQ1 : List Nat := [1, 2, 3]

/-- A second size-3 quorum, sharing nodes `2` and `3` with `negQ1`. -/
def negQ2 : List Nat := [2, 3, 4]

def negVotes : VoteLog Nat Nat := [(1, 0), (2, 0), (3, 0), (2, 1), (3, 1), (4, 1)]

/-- **The necessity face.** Two valid `2f+1`-of-`3f+1` quorums unanimously certify DIFFERENT
    outcomes (`0 ≠ 1`) — consistency fails outright once equivocation is unconstrained. This
    is possible only because `negVotes` lets nodes `2` and `3` equivocate; `NoEquivocation`
    is exactly the hypothesis that rules this scenario out. -/
theorem equivocation_breaks_consistency :
    IsQuorum negNodes 1 negQ1 ∧ IsQuorum negNodes 1 negQ2 ∧
    Certifies negVotes negQ1 (0 : Nat) ∧ Certifies negVotes negQ2 (1 : Nat) ∧ (0 : Nat) ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold IsQuorum; decide
  · unfold IsQuorum; decide
  · unfold Certifies; decide
  · unfold Certifies; decide
  · decide

/-- Confirming the shared nodes equivocate — `NoEquivocation negVotes faulty` fails
    for any `faulty` set not containing both `2` and `3` (in particular for `faulty = []`,
    the "everyone is nominally correct" reading), which is exactly why the positive theorem's
    hypothesis is essential here, not vacuously available. -/
example : ¬ NoEquivocation negVotes ([] : List Nat) := by
  unfold NoEquivocation
  intro h
  have := h (2, 0) (by decide) (2, 1) (by decide) rfl (by decide)
  exact absurd this (by decide)

/-! ### (c) Instance — an honest `n = 4, f = 1` run -/

/-- The same `n = 4, f = 1` universe and quorums, with an honest vote log: every voter
    records the SAME outcome `7` exactly once. -/
def posVotes : VoteLog Nat Nat := [(1, 7), (2, 7), (3, 7), (4, 7)]

example : (7 : Nat) = 7 :=
  equivocation_aware_consistent (nodes := negNodes) (f := 1) (faulty := ([] : List Nat))
    (votes := posVotes) (q1 := negQ1) (q2 := negQ2) (A := 7) (B := 7)
    (by decide) (by decide) (by unfold IsQuorum; decide) (by unfold IsQuorum; decide)
    (by decide) (by unfold NoEquivocation; decide) (by unfold Certifies; decide)
    (by unfold Certifies; decide)

end AutoproverCorpus.EquivocationAwareQuorum
