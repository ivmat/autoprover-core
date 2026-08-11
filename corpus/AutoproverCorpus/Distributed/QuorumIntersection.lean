/-
  AutoproverCorpus.Distributed.QuorumIntersection

  Quorum intersection: any two majority subsets of a finite set share a member, so two
  majorities can never certify contradictory outcomes.

  Attribution: Classical (majority quorums; Thomas, 1979; Gifford, 1979).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.QuorumIntersection

variable {V : Type u} [DecidableEq V]

/-- A quorum `q` is a MAJORITY of universe `u` when it holds strictly more than half of
    `u`'s (deduplicated) voters. -/
abbrev IsMajority (u q : List V) : Prop := 2 * q.length > u.length

/-! ### (1) The counting lemma core Lean does not supply -/

/-- A `Nodup` list that is a `Subset` of another list is no longer than it. Core Lean
    4.31 has no lemma of this shape (checked by grep: `List.Sublist.length_le` exists
    for the order-preserving `Sublist` relation, but nothing transports `Nodup` along
    the weaker `Subset` relation) — hand-proved here by induction on the `Nodup` list,
    peeling off the head element via `List.append_of_mem` (which needs no
    `DecidableEq`/`BEq` instance) at each step. -/
theorem length_le_of_subset_of_nodup {α : Type u} :
    ∀ {l1 l2 : List α}, l1.Nodup → l1 ⊆ l2 → l1.length ≤ l2.length
  | [], _, _, _ => by simp
  | a :: t, l2, h1, hsub => by
      rw [List.nodup_cons] at h1
      obtain ⟨hat, ht⟩ := h1
      have ha : a ∈ l2 := hsub List.mem_cons_self
      obtain ⟨s, u, rfl⟩ := List.append_of_mem ha
      have htsub : t ⊆ s ++ u := by
        intro x hx
        have hxl2 : x ∈ s ++ (a :: u) := hsub (List.mem_cons_of_mem a hx)
        rcases List.mem_append.mp hxl2 with hxs | hxau
        · exact List.mem_append_left u hxs
        · rcases List.mem_cons.mp hxau with hxa | hxu
          · exact absurd (hxa ▸ hx) hat
          · exact List.mem_append_right s hxu
      have hlen := length_le_of_subset_of_nodup ht htsub
      simp only [List.length_cons, List.length_append] at hlen ⊢
      omega

/-! ### (2) The core theorem -/

omit [DecidableEq V] in
/-- **Quorum intersection.** Any two majority quorums of the same `Nodup` universe
    share at least one common voter. Proof route: if `q1` and `q2` were disjoint,
    `q1 ++ q2` would be a `Nodup` subset of `u` (by `List.nodup_append` and the
    subset hypotheses), so by the counting lemma
    `q1.length + q2.length ≤ u.length`; but both being majorities gives
    `2 * q1.length > u.length` and `2 * q2.length > u.length`, summing to
    `2 * (q1.length + q2.length) > 2 * u.length`, i.e.
    `q1.length + q2.length > u.length` — contradiction. -/
theorem quorum_intersect {u q1 q2 : List V}
    (_hu : u.Nodup) (hq1 : q1.Nodup) (hq2 : q2.Nodup)
    (hsub1 : q1 ⊆ u) (hsub2 : q2 ⊆ u)
    (hmaj1 : IsMajority u q1) (hmaj2 : IsMajority u q2) :
    ∃ v, v ∈ q1 ∧ v ∈ q2 := by
  apply Classical.byContradiction
  intro hno
  have hdisj : ∀ a ∈ q1, ∀ b ∈ q2, a ≠ b := by
    intro a ha b hb heq
    exact hno ⟨a, ha, heq ▸ hb⟩
  have hnodupApp : (q1 ++ q2).Nodup := List.nodup_append.mpr ⟨hq1, hq2, hdisj⟩
  have hsubApp : (q1 ++ q2) ⊆ u := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact hsub1 hx1
    · exact hsub2 hx2
  have hlenApp : (q1 ++ q2).length ≤ u.length :=
    length_le_of_subset_of_nodup hnodupApp hsubApp
  simp only [List.length_append] at hlenApp
  unfold IsMajority at hmaj1 hmaj2
  omega

/-! ### (3) The trust payload: unambiguous certification -/

omit [DecidableEq V] in
/-- **No conflicting certification.** If `q1` unanimously votes outcome `A` and `q2`
    unanimously votes outcome `B`, and both are majority quorums of the same universe,
    then `A = B`: a quorum-certified verdict is unambiguous, because quorum intersection
    forces a shared voter, and that voter cannot have cast two different votes. -/
theorem no_conflicting_certification {Outcome : Type v} [DecidableEq Outcome]
    {u q1 q2 : List V} {vote : V → Outcome} {A B : Outcome}
    (hu : u.Nodup) (hq1 : q1.Nodup) (hq2 : q2.Nodup)
    (hsub1 : q1 ⊆ u) (hsub2 : q2 ⊆ u)
    (hmaj1 : IsMajority u q1) (hmaj2 : IsMajority u q2)
    (hvoteA : ∀ v ∈ q1, vote v = A) (hvoteB : ∀ v ∈ q2, vote v = B) :
    A = B := by
  obtain ⟨v, hv1, hv2⟩ := quorum_intersect hu hq1 hq2 hsub1 hsub2 hmaj1 hmaj2
  rw [← hvoteA v hv1, ← hvoteB v hv2]

/-! ### (4) Instances: concrete examples -/

/-- A concrete 3-voter universe. -/
def sampleUniverse : List Nat := [1, 2, 3]

/-- A size-2 majority of `sampleUniverse`. -/
def sampleQ1 : List Nat := [1, 2]

/-- A second size-2 majority of `sampleUniverse`, overlapping `sampleQ1` at `2`. -/
def sampleQ2 : List Nat := [2, 3]

example : sampleUniverse.Nodup := by decide
example : sampleQ1.Nodup := by decide
example : sampleQ2.Nodup := by decide
example : sampleQ1 ⊆ sampleUniverse := by decide
example : sampleQ2 ⊆ sampleUniverse := by decide
example : IsMajority sampleUniverse sampleQ1 := by decide
example : IsMajority sampleUniverse sampleQ2 := by decide

/-- `quorum_intersect` applied to the concrete example: `sampleQ1` and `sampleQ2` share
    a voter (namely `2`). -/
example : ∃ v, v ∈ sampleQ1 ∧ v ∈ sampleQ2 :=
  quorum_intersect (u := sampleUniverse) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- The majority threshold is essential, not vacuous: a size-1 subset of the same
    3-voter universe is not a majority (`2 * 1 = 2 ≤ 3`, not `> 3`). -/
example : ¬ IsMajority sampleUniverse ([1] : List Nat) := by decide

end AutoproverCorpus.QuorumIntersection
