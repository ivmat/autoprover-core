/-
  AutoproverCorpus.Distributed.WeightedVotingQuorum

  Gifford's weighted-voting quorum condition, in full generality: for an arbitrary voter type,
  an arbitrary assignment of votes (weights) to voters, and arbitrary read/write quorums given
  as selections of voters, IF the two quorums together gather strictly more votes than the
  system holds in total THEN they share a voter. The two classical corollaries follow directly:
  `R + W > N` makes every read quorum meet every write quorum, and `W + W > N` makes any two
  write quorums meet.

  This generalizes this corpus's `Distributed.QuorumIntersection`, which is the unweighted
  majority case (every voter carries one vote, both quorums are majorities). Here the votes are
  arbitrary naturals, the two thresholds may differ (the asymmetric read/write design Gifford
  introduced), and the intersection hypothesis is a single inequality about gathered votes.

  The hypothesis is TIGHT, not merely sufficient: with total votes `N = 8` and two quorums of
  4 votes each (`R + W = N`, one vote short), an explicit pair of DISJOINT quorums is exhibited
  below (`tight_witness`) — so the strict inequality cannot be weakened to `≥`.

  Attribution: D. K. Gifford, "Weighted Voting for Replicated Data", 1979 (the unweighted
  majority-consensus ancestor is R. H. Thomas, 1979).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.WeightedVotingQuorum

variable {α : Type}

/-! ### Voters, votes, and quorums -/

/-- The votes a selection `q` gathers from the voter list `U`: the total weight of the
    selected voters. A quorum is exactly such a selection whose gathered votes clear a
    threshold; nothing here assumes the selection is a majority, or even nonempty. -/
def votes (w : α → Nat) (U : List α) (q : α → Bool) : Nat :=
  ((U.filter q).map w).sum

/-- The votes the whole system holds: every voter's weight, counted once. Written `N` in
    Gifford's `R + W > N` condition. -/
def totalVotes (w : α → Nat) (U : List α) : Nat :=
  (U.map w).sum

/-- No selection can gather more than the system holds. -/
theorem votes_le_totalVotes (w : α → Nat) (U : List α) (q : α → Bool) :
    votes w U q ≤ totalVotes w U := by
  induction U with
  | nil => simp [votes, totalVotes]
  | cons x xs ih =>
    unfold votes totalVotes at ih ⊢
    by_cases h : q x = true
    · rw [List.filter_cons_of_pos (by simpa using h)]
      simp only [List.map_cons, List.sum_cons]
      omega
    · rw [List.filter_cons_of_neg (by simpa using h)]
      simp only [List.map_cons, List.sum_cons]
      omega

/-! ### The counting core: disjoint quorums cannot oversubscribe the electorate -/

/-- **The counting lemma.** Two selections that share no voter of `U` gather, between them, at
    most the votes the system holds — each voter contributes its weight to at most one of the
    two sums. Proved by induction on the voter list: at each voter, the disjointness hypothesis
    rules out the one case (selected by both) in which its weight would be double-counted. -/
theorem disjoint_votes_le (w : α → Nat) (U : List α) {q1 q2 : α → Bool}
    (hdis : ∀ a, a ∈ U → q1 a = true → q2 a = true → False) :
    votes w U q1 + votes w U q2 ≤ totalVotes w U := by
  induction U with
  | nil => simp [votes, totalVotes]
  | cons x xs ih =>
    have hmem : x ∈ x :: xs := by simp
    have ih' := ih (fun a ha => hdis a (List.mem_cons_of_mem x ha))
    unfold votes totalVotes at ih' ⊢
    by_cases h1 : q1 x = true
    · have h2 : q2 x = false := by
        cases hq : q2 x with
        | false => rfl
        | true => exact absurd (hdis x hmem h1 hq) (fun h => h)
      rw [List.filter_cons_of_pos (by simpa using h1),
          List.filter_cons_of_neg (by simp [h2])]
      simp only [List.map_cons, List.sum_cons]
      omega
    · rw [List.filter_cons_of_neg (by simpa using h1)]
      by_cases h2 : q2 x = true
      · rw [List.filter_cons_of_pos (by simpa using h2)]
        simp only [List.map_cons, List.sum_cons]
        omega
      · rw [List.filter_cons_of_neg (by simpa using h2)]
        simp only [List.map_cons, List.sum_cons]
        omega

/-! ### Gifford's quorum-intersection theorem -/

/-- **Weighted-voting quorum intersection (general form).** If two quorums gather, between
    them, strictly more votes than the system holds, some voter belongs to both. Contrapositive
    of the counting lemma: were they disjoint, their votes would fit inside the electorate.
    Note the conclusion is a *shared voter of `U`* — selections agreeing outside the voter list
    are irrelevant, as they should be. -/
theorem quorums_intersect (w : α → Nat) (U : List α) (q1 q2 : α → Bool)
    (h : totalVotes w U < votes w U q1 + votes w U q2) :
    ∃ a, a ∈ U ∧ q1 a = true ∧ q2 a = true := by
  refine Classical.byContradiction (fun hno => ?_)
  have hdis : ∀ a, a ∈ U → q1 a = true → q2 a = true → False :=
    fun a ha h1 h2 => hno ⟨a, ha, h1, h2⟩
  have := disjoint_votes_le w U hdis
  omega

/-- **Read/write intersection (`R + W > N`).** A read quorum gathering at least `R` votes and a
    write quorum gathering at least `W` votes share a voter whenever `R + W` exceeds the total
    vote count `N` — so no read can miss the latest committed write. -/
theorem read_write_intersect (w : α → Nat) (U : List α) (R W : Nat)
    (hRW : totalVotes w U < R + W)
    (qr qw : α → Bool) (hr : R ≤ votes w U qr) (hw : W ≤ votes w U qw) :
    ∃ a, a ∈ U ∧ qr a = true ∧ qw a = true :=
  quorums_intersect w U qr qw (by omega)

/-- **Write/write intersection (`2W > N`).** Two write quorums share a voter whenever twice the
    write threshold exceeds the total vote count — so two concurrent writes cannot both commit
    without a common witness. -/
theorem write_write_intersect (w : α → Nat) (U : List α) (W : Nat)
    (hW : totalVotes w U < W + W)
    (qw1 qw2 : α → Bool) (h1 : W ≤ votes w U qw1) (h2 : W ≤ votes w U qw2) :
    ∃ a, a ∈ U ∧ qw1 a = true ∧ qw2 a = true :=
  quorums_intersect w U qw1 qw2 (by omega)

/-! ### Instance: a concrete 5-voter weighted system, and the tightness witness -/

/-- Five replicas holding a weighted vote each. -/
inductive Voter where
  | v0 | v1 | v2 | v3 | v4
  deriving DecidableEq

open Voter

/-- Gifford's asymmetric assignment: one heavyweight replica (3 votes), one middleweight
    (2 votes), three lightweights (1 vote each) — eight votes in all. -/
abbrev wt : Voter → Nat
  | .v0 => 3
  | .v1 => 2
  | .v2 => 1
  | .v3 => 1
  | .v4 => 1

abbrev U : List Voter := [v0, v1, v2, v3, v4]

/-- The system holds `N = 8` votes. -/
example : totalVotes wt U = 8 := by decide

/-- A read quorum of `R = 4` votes: the heavyweight plus one lightweight. -/
abbrev qRead : Voter → Bool
  | .v0 => true
  | .v3 => true
  | _ => false

/-- A write quorum of `W = 5` votes: everyone except the heavyweight. -/
abbrev qWrite : Voter → Bool
  | .v0 => false
  | _ => true

example : votes wt U qRead = 4 := by decide
example : votes wt U qWrite = 5 := by decide

/-- **Non-vacuity.** With `R + W = 9 > 8 = N`, the general theorem yields an actual shared
    voter for this concrete read/write pair (it is `v3`) — the intersection claim is exercised,
    not merely asserted about hypothetical quorums. -/
example : ∃ a, a ∈ U ∧ qRead a = true ∧ qWrite a = true :=
  read_write_intersect wt U 4 5 (by decide) qRead qWrite (by decide) (by decide)

/-- The witness, named: `v3` carries both quorums. -/
example : v3 ∈ U ∧ qRead v3 = true ∧ qWrite v3 = true := by decide

/-! #### Tightness: `≥` is not enough -/

/-- A 4-vote quorum: heavyweight plus one lightweight. -/
abbrev qA : Voter → Bool
  | .v0 => true
  | .v2 => true
  | _ => false

/-- A disjoint 4-vote quorum: middleweight plus the other two lightweights. -/
abbrev qB : Voter → Bool
  | .v1 => true
  | .v3 => true
  | .v4 => true
  | _ => false

/-- **The hypothesis is tight.** Both quorums gather 4 votes, so `R + W = 8 = N` — one short of
    the strict inequality — and they are DISJOINT: no voter is selected by both. So
    `quorums_intersect` cannot be weakened from `N < R + W` to `N ≤ R + W`, and Gifford's
    condition is necessary, not just sufficient. -/
theorem tight_witness :
    votes wt U qA = 4 ∧ votes wt U qB = 4 ∧ totalVotes wt U = 8 ∧
      ∀ a, a ∈ U → qA a = true → qB a = true → False := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro a _ h1 h2
  cases a <;> simp_all

end AutoproverCorpus.WeightedVotingQuorum
