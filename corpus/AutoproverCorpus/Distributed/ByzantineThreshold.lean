/-
  AutoproverCorpus.Distributed.ByzantineThreshold

  Byzantine quorum intersection: with the node universe of size at most 3f+1, any two quorums of
  size at least 2f+1 intersect in at least f+1 nodes, hence in at least one correct node. The
  size bound on the universe is essential: a larger universe admits disjoint quorums.

  Attribution: Classical (Pease, Shostak and Lamport, 1980; Bracha; Castro and Liskov, 1999).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Distributed.QuorumIntersection

namespace AutoproverCorpus.ByzantineThreshold

variable {V : Type u} [DecidableEq V]

/-! ### A hand-proved filter-split counting lemma (core Lean has none of this shape) -/

/-- Splitting a list by a Boolean predicate accounts for every element exactly once:
    the lengths of the "kept" and "dropped" filters sum to the original length. Core
    Lean 4.31 has `List.length_eq_countP_add_countP`, stated via a `Prop`-level `¬p a`
    on a `Bool`-valued `p`; this file avoids depending on that coercion and hand-proves
    the `Bool`-level statement directly by induction, using `List.filter_cons_of_pos`/
    `List.filter_cons_of_neg`. -/
theorem filter_split_length {α : Type u} (p : α → Bool) :
    ∀ (l : List α), (l.filter p).length + (l.filter (fun a => !p a)).length = l.length
  | [] => by simp
  | a :: t => by
      cases hb : p a with
      | false =>
          have h1 : List.filter p (a :: t) = List.filter p t :=
            List.filter_cons_of_neg (by simp [hb])
          have h2 : List.filter (fun x => !p x) (a :: t) = a :: List.filter (fun x => !p x) t :=
            List.filter_cons_of_pos (by simp [hb])
          rw [h1, h2]
          simp only [List.length_cons]
          have ih := filter_split_length p t
          omega
      | true =>
          have h1 : List.filter p (a :: t) = a :: List.filter p t :=
            List.filter_cons_of_pos hb
          have h2 : List.filter (fun x => !p x) (a :: t) = List.filter (fun x => !p x) t :=
            List.filter_cons_of_neg (by simp [hb])
          rw [h1, h2]
          simp only [List.length_cons]
          have ih := filter_split_length p t
          omega

/-! ### The intersection representative -/

/-- A concrete list representative of `q1 ∩ q2`: the elements of `q2` that are also
    members of `q1`. -/
def interOf (q1 q2 : List V) : List V := q2.filter (fun x => decide (x ∈ q1))

/-- The complementary "not-in-`q1`" part of `q2`. -/
def diffOf (q1 q2 : List V) : List V := q2.filter (fun x => !decide (x ∈ q1))

/-- A concrete list representative of `q1 ∪ q2`: `q1` followed by the part of `q2` not
    already in `q1`. -/
def unionOf (q1 q2 : List V) : List V := q1 ++ diffOf q1 q2

/-! ### (a) THE SUBSTANCE — the inclusion-exclusion-style counting bound -/

theorem inter_size_ge {nodes q1 q2 : List V}
    (_hnodes : nodes.Nodup) (hq1 : q1.Nodup) (hq2 : q2.Nodup)
    (hsub1 : q1 ⊆ nodes) (hsub2 : q2 ⊆ nodes) :
    q1.length + q2.length ≤ nodes.length + (interOf q1 q2).length := by
  have hsplit : (interOf q1 q2).length + (diffOf q1 q2).length = q2.length :=
    filter_split_length (fun x => decide (x ∈ q1)) q2
  have hdiffSub : diffOf q1 q2 ⊆ q2 := fun x hx => (List.mem_filter.mp hx).1
  have hdiffSubNodes : diffOf q1 q2 ⊆ nodes := fun x hx => hsub2 (hdiffSub hx)
  have hdiffNodup : (diffOf q1 q2).Nodup :=
    List.Nodup.sublist List.filter_sublist hq2
  have hdisj : ∀ a ∈ q1, ∀ b ∈ diffOf q1 q2, a ≠ b := by
    intro a ha b hb heq
    have hbmem : b ∈ q2 ∧ (!decide (b ∈ q1)) = true := List.mem_filter.mp hb
    have : decide (b ∈ q1) = true := by simp [heq ▸ ha]
    rw [this] at hbmem
    simp at hbmem
  have hunionNodup : (unionOf q1 q2).Nodup :=
    List.nodup_append.mpr ⟨hq1, hdiffNodup, hdisj⟩
  have hunionSub : unionOf q1 q2 ⊆ nodes := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact hsub1 hx1
    · exact hdiffSubNodes hx2
  have hunionLen : (unionOf q1 q2).length ≤ nodes.length :=
    AutoproverCorpus.QuorumIntersection.length_le_of_subset_of_nodup hunionNodup hunionSub
  have hunionEq : (unionOf q1 q2).length = q1.length + (diffOf q1 q2).length := by
    unfold unionOf
    rw [List.length_append]
  omega

/-- **Byzantine quorum intersection size.** With `nodes.length ≤ 3f+1` and both `q1`,
    `q2` of size `≥ 2f+1`, the intersection has length `≥ f+1`: any two Byzantine
    quorums share at least `f+1` nodes. -/
theorem byzantine_intersect_size {nodes q1 q2 : List V} {f : Nat}
    (hnodes : nodes.Nodup) (hq1 : q1.Nodup) (hq2 : q2.Nodup)
    (hsub1 : q1 ⊆ nodes) (hsub2 : q2 ⊆ nodes)
    (hn : nodes.length ≤ 3 * f + 1)
    (hq1len : 2 * f + 1 ≤ q1.length) (hq2len : 2 * f + 1 ≤ q2.length) :
    f + 1 ≤ (interOf q1 q2).length := by
  have hbound := inter_size_ge hnodes hq1 hq2 hsub1 hsub2
  omega

/-! ### (b) The correctness payload -/

/-- **Correct-node witness.** Given a faulty set of size `≤ f`, any two `2f+1`-of-`3f+1`
    Byzantine quorums share a node that is NOT faulty — a CORRECT node. Proof: if every
    shared node were faulty, the (`Nodup`) intersection would be a subset of `faulty`,
    forcing its length `≤ f` by the imported counting lemma, contradicting
    `byzantine_intersect_size`'s `≥ f+1` bound. -/
theorem byzantine_correct_witness {nodes q1 q2 faulty : List V} {f : Nat}
    (hnodes : nodes.Nodup) (hq1 : q1.Nodup) (hq2 : q2.Nodup)
    (hsub1 : q1 ⊆ nodes) (hsub2 : q2 ⊆ nodes)
    (hn : nodes.length ≤ 3 * f + 1)
    (hq1len : 2 * f + 1 ≤ q1.length) (hq2len : 2 * f + 1 ≤ q2.length)
    (hfaultylen : faulty.length ≤ f) :
    ∃ v, v ∈ q1 ∧ v ∈ q2 ∧ v ∉ faulty := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ v ∈ q1, v ∈ q2 → v ∈ faulty := by
    intro v hv1 hv2
    apply Classical.byContradiction
    intro hnf
    exact hno ⟨v, hv1, hv2, hnf⟩
  have hinterSub : interOf q1 q2 ⊆ faulty := by
    intro x hx
    have hxmem : x ∈ q2 ∧ decide (x ∈ q1) = true := List.mem_filter.mp hx
    exact hall x (of_decide_eq_true hxmem.2) hxmem.1
  have hinterNodup : (interOf q1 q2).Nodup :=
    List.Nodup.sublist List.filter_sublist hq2
  have hinterLen : (interOf q1 q2).length ≤ faulty.length :=
    AutoproverCorpus.QuorumIntersection.length_le_of_subset_of_nodup hinterNodup hinterSub
  have hbig : f + 1 ≤ (interOf q1 q2).length :=
    byzantine_intersect_size hnodes hq1 hq2 hsub1 hsub2 hn hq1len hq2len
  omega

/-! ### (c) Instances by `decide` -/

/-- The canonical `n = 4, f = 1` universe. -/
def sampleNodes : List Nat := [1, 2, 3, 4]

/-- A size-3 (`2f+1`) Byzantine quorum. -/
def sampleQ1 : List Nat := [1, 2, 3]

/-- A second size-3 Byzantine quorum. -/
def sampleQ2 : List Nat := [2, 3, 4]

/-- `sampleQ1` and `sampleQ2` share `2` nodes (`≥ f+1 = 2` for `f = 1`). -/
example : interOf sampleQ1 sampleQ2 = [2, 3] := by decide

example : 2 ≤ (interOf sampleQ1 sampleQ2).length := by decide

/-- The general theorem specialized to this concrete instance. -/
example : 1 + 1 ≤ (interOf sampleQ1 sampleQ2).length :=
  byzantine_intersect_size (f := 1) (nodes := sampleNodes) (q1 := sampleQ1) (q2 := sampleQ2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- **Tightness witness.** The `2f+1` threshold is not merely sufficient — size-`2f`
    quorums do NOT suffice: two disjoint size-2 quorums exist in the same 4-node
    universe. -/
def sampleQ1' : List Nat := [1, 2]

def sampleQ2' : List Nat := [3, 4]

example : interOf sampleQ1' sampleQ2' = [] := by decide

end AutoproverCorpus.ByzantineThreshold
