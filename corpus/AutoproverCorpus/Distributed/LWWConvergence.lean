/-
  AutoproverCorpus.Distributed.LWWConvergence

  Last-writer-wins register: two concrete instances, not a general biconditional. (i) With no
  tie-break, merge fails commutativity and convergence on equal-timestamp distinct writes; (ii)
  with a total lexicographic tie-break, merge is commutative, associative and idempotent, hence
  replicas converge.

  Attribution: Classical (last-writer-wins register; Shapiro, Preguica, Baquero and Zawirski,
  2011).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Distributed.ReplicaConvergence

namespace AutoproverCorpus.LWWConvergence

/-- A write: `(timestamp, value)`. `abbrev`, not `def` — `decide`-checked examples below
    need `DecidableEq Write` to see straight through to `Nat × Nat`'s own instance. -/
abbrev Write : Type := Nat × Nat

/-! ### The naive merge — no tie-break on equal timestamps; refuted below. -/

/-- Naive LWW merge: larger timestamp wins; on an equal timestamp, keep the first
    argument — no tie-break on value at all. -/
def lwwNaive (a b : Write) : Write := if a.1 < b.1 then b else a

/-! ### (A) Refutation -/

/-- **(A) `lwwNaive` is not even commutative.** Witness: `(1,0)` and `(1,1)`
    share timestamp `1` but carry distinct values; the naive merge picks whichever
    argument came first, so swapping the arguments changes the answer. -/
theorem lwwNaive_not_comm : ¬ AutoproverCorpus.ReplicaConvergence.Comm lwwNaive := by
  intro h
  have h2 := h (1, 0) (1, 1)
  exact absurd h2 (by decide)

/-- **(A), sharpened to convergence itself.** `[(1,0),(1,1)]` and `[(1,1),(1,0)]` are
    permutations of one another (hence `SameUpdates`, via `SameUpdates.perm`), yet
    folding them with `lwwNaive` from the same start state reaches different final
    states. The no-tie-break LWW register does not converge — stated as "breaks",
    not as a convergence result. -/
theorem lwwNaive_breaks_convergence :
    ∃ (s : Write) (l1 l2 : List Write),
      AutoproverCorpus.ReplicaConvergence.SameUpdates l1 l2 ∧
        AutoproverCorpus.ReplicaConvergence.fold lwwNaive s l1 ≠
          AutoproverCorpus.ReplicaConvergence.fold lwwNaive s l2 := by
  refine ⟨(0, 0), [(1, 0), (1, 1)], [(1, 1), (1, 0)], ?_, ?_⟩
  · exact AutoproverCorpus.ReplicaConvergence.SameUpdates.perm (List.Perm.swap (1, 1) (1, 0) [])
  · decide

/-! ### The total-tie-break order and merge — the correct merge. -/

/-- The total lexicographic order on writes: larger timestamp wins; on a tie, larger
    value wins — a total tie-break (unlike `lwwNaive`'s "first argument" rule). `abbrev`
    so `Decidable` instance search sees straight through it. -/
abbrev lwwLe (a b : Write) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

/-- Correct LWW merge: the max of `a`, `b` under the total order `lwwLe`. -/
def lwwTotal (a b : Write) : Write := if lwwLe a b then b else a

/-! ### (B) `lwwLe` is a genuine total order. -/

theorem lwwLe_refl (a : Write) : lwwLe a a := by
  obtain ⟨a1, a2⟩ := a
  unfold lwwLe
  omega

theorem lwwLe_total (a b : Write) : lwwLe a b ∨ lwwLe b a := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  unfold lwwLe
  omega

theorem lwwLe_antisymm {a b : Write} (h1 : lwwLe a b) (h2 : lwwLe b a) : a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  unfold lwwLe at h1 h2
  have e1 : a1 = b1 := by omega
  have e2 : a2 = b2 := by omega
  subst e1; subst e2; rfl

theorem lwwLe_trans {a b c : Write} (hab : lwwLe a b) (hbc : lwwLe b c) : lwwLe a c := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨c1, c2⟩ := c
  unfold lwwLe at hab hbc ⊢
  omega

/-- `lwwLe a b → a.1 ≤ b.1` — a genuine lexicographic order never decreases the
    timestamp. -/
theorem lwwLe_timestamp_le {a b : Write} (h : lwwLe a b) : a.1 ≤ b.1 := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  unfold lwwLe at h
  omega

/-! ### (B) `lwwTotal` is an upper bound / least upper bound under `lwwLe`. -/

theorem le_lwwTotal_left (a b : Write) : lwwLe a (lwwTotal a b) := by
  unfold lwwTotal
  by_cases h : lwwLe a b
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact lwwLe_refl a

theorem le_lwwTotal_right (a b : Write) : lwwLe b (lwwTotal a b) := by
  unfold lwwTotal
  by_cases h : lwwLe a b
  · rw [if_pos h]; exact lwwLe_refl b
  · rw [if_neg h]
    rcases lwwLe_total a b with h' | h'
    · exact absurd h' h
    · exact h'

/-- `lwwTotal a b` is the LEAST upper bound of `a`, `b` under `lwwLe`: any `c` above
    both is above `lwwTotal a b`. The join-semilattice fact `lwwTotal_assoc` rests on. -/
theorem lwwTotal_least_upper_bound (a b c : Write) (ha : lwwLe a c) (hb : lwwLe b c) :
    lwwLe (lwwTotal a b) c := by
  unfold lwwTotal
  by_cases h : lwwLe a b
  · rw [if_pos h]; exact hb
  · rw [if_neg h]; exact ha

/-- `lwwTotal a b` is literally one of its two arguments — never a synthesized third
    value. -/
theorem lwwTotal_eq_or (a b : Write) : lwwTotal a b = a ∨ lwwTotal a b = b := by
  unfold lwwTotal
  by_cases h : lwwLe a b
  · rw [if_pos h]; right; rfl
  · rw [if_neg h]; left; rfl

theorem lwwTotal_comm : AutoproverCorpus.ReplicaConvergence.Comm lwwTotal := by
  intro a b
  by_cases hab : lwwLe a b
  · by_cases hba : lwwLe b a
    · have heq : a = b := lwwLe_antisymm hab hba
      subst heq; rfl
    · simp [lwwTotal, hab, hba]
  · by_cases hba : lwwLe b a
    · simp [lwwTotal, hab, hba]
    · exfalso
      rcases lwwLe_total a b with h | h
      · exact hab h
      · exact hba h

/-- **Associativity — the substantive case (needs totality/antisymmetry/transitivity of
    the tie-break; `lwwNaive` lacks exactly this).** Both `lwwTotal (lwwTotal a b) c`
    and `lwwTotal a (lwwTotal b c)` dominate `a`, `b`, `c` under `lwwLe`, and each is a
    least upper bound of the other's dominated pair — mutual `lwwLe`, hence equal by
    `lwwLe_antisymm`. -/
theorem lwwTotal_assoc : AutoproverCorpus.ReplicaConvergence.Assoc lwwTotal := by
  intro a b c
  have hX_c : lwwLe c (lwwTotal (lwwTotal a b) c) := le_lwwTotal_right (lwwTotal a b) c
  have hX_ab : lwwLe (lwwTotal a b) (lwwTotal (lwwTotal a b) c) :=
    le_lwwTotal_left (lwwTotal a b) c
  have hX_a : lwwLe a (lwwTotal (lwwTotal a b) c) :=
    lwwLe_trans (le_lwwTotal_left a b) hX_ab
  have hX_b : lwwLe b (lwwTotal (lwwTotal a b) c) :=
    lwwLe_trans (le_lwwTotal_right a b) hX_ab
  have hY_a : lwwLe a (lwwTotal a (lwwTotal b c)) := le_lwwTotal_left a (lwwTotal b c)
  have hY_bc : lwwLe (lwwTotal b c) (lwwTotal a (lwwTotal b c)) :=
    le_lwwTotal_right a (lwwTotal b c)
  have hY_b : lwwLe b (lwwTotal a (lwwTotal b c)) :=
    lwwLe_trans (le_lwwTotal_left b c) hY_bc
  have hY_c : lwwLe c (lwwTotal a (lwwTotal b c)) :=
    lwwLe_trans (le_lwwTotal_right b c) hY_bc
  have hXY : lwwLe (lwwTotal (lwwTotal a b) c) (lwwTotal a (lwwTotal b c)) := by
    have h1 : lwwLe (lwwTotal a b) (lwwTotal a (lwwTotal b c)) :=
      lwwTotal_least_upper_bound a b _ hY_a hY_b
    exact lwwTotal_least_upper_bound (lwwTotal a b) c _ h1 hY_c
  have hYX : lwwLe (lwwTotal a (lwwTotal b c)) (lwwTotal (lwwTotal a b) c) := by
    have h1 : lwwLe (lwwTotal b c) (lwwTotal (lwwTotal a b) c) :=
      lwwTotal_least_upper_bound b c _ hX_b hX_c
    exact lwwTotal_least_upper_bound a (lwwTotal b c) _ hX_a h1
  exact lwwLe_antisymm hXY hYX

theorem lwwTotal_idem : AutoproverCorpus.ReplicaConvergence.Idem lwwTotal := by
  intro a
  unfold lwwTotal
  by_cases h : lwwLe a a
  · rw [if_pos h]
  · rw [if_neg h]

theorem lww_convergence (s : Write) {l1 l2 : List Write}
    (h : AutoproverCorpus.ReplicaConvergence.SameUpdates l1 l2) :
    AutoproverCorpus.ReplicaConvergence.fold lwwTotal s l1 =
      AutoproverCorpus.ReplicaConvergence.fold lwwTotal s l2 :=
  AutoproverCorpus.ReplicaConvergence.convergence lwwTotal_comm lwwTotal_assoc lwwTotal_idem s h

/-! ### (C) "keeps the max-timestamp write" — naming the claim honestly. -/

/-- `lwwTotal a b`'s timestamp is always the larger of the two. -/
theorem lwwTotal_timestamp (a b : Write) : (lwwTotal a b).1 = max a.1 b.1 := by
  have h1 : a.1 ≤ (lwwTotal a b).1 := lwwLe_timestamp_le (le_lwwTotal_left a b)
  have h2 : b.1 ≤ (lwwTotal a b).1 := lwwLe_timestamp_le (le_lwwTotal_right a b)
  rcases lwwTotal_eq_or a b with h | h <;> rw [h] at h1 h2 ⊢ <;> omega

/-- If the two timestamps DIFFER, `lwwTotal` is literally whichever argument carries the
    larger one — the value-based tie-break only ever decides EQUAL-timestamp cases,
    never overrides a genuine timestamp difference. This substantiates the name
    "last-writer-wins". -/
theorem lwwTotal_picks_later {a b : Write} (h : a.1 ≠ b.1) :
    lwwTotal a b = (if a.1 < b.1 then b else a) := by
  unfold lwwTotal
  by_cases hlt : a.1 < b.1
  · have hle : lwwLe a b := Or.inl hlt
    rw [if_pos hle, if_pos hlt]
  · have hnle : ¬ lwwLe a b := by
      intro hle
      rcases hle with hle | ⟨he, _⟩
      · exact hlt hle
      · exact h he
    rw [if_neg hnle, if_neg hlt]

/-! ### (D) Instances and a counterexample. -/

/-- A reorder (`List.Perm`) followed by a `dup` redelivery, chained via `trans` — two
    different concrete histories, `SameUpdates`-related. -/
theorem lwwTotal_histories_same_updates :
    AutoproverCorpus.ReplicaConvergence.SameUpdates
      ([(1, 5), (2, 3)] : List Write) [(2, 3), (1, 5), (1, 5)] := by
  have hperm : AutoproverCorpus.ReplicaConvergence.SameUpdates
      ([(1, 5), (2, 3)] : List Write) [(2, 3), (1, 5)] :=
    AutoproverCorpus.ReplicaConvergence.SameUpdates.perm (List.Perm.swap (2, 3) (1, 5) [])
  have hdup : AutoproverCorpus.ReplicaConvergence.SameUpdates
      (([(2, 3)] : List Write) ++ (1, 5) :: (1, 5) :: []) ([(2, 3)] ++ (1, 5) :: []) :=
    AutoproverCorpus.ReplicaConvergence.SameUpdates.dup (1, 5)
  exact AutoproverCorpus.ReplicaConvergence.SameUpdates.trans hperm hdup.symm

/-- Instance (positive half): the two different histories above — a
    reorder plus a redelivered duplicate — fold to the same state under `lwwTotal`. -/
theorem lwwTotal_two_histories_converge :
    AutoproverCorpus.ReplicaConvergence.fold lwwTotal (0, 0) ([(1, 5), (2, 3)] : List Write) =
      AutoproverCorpus.ReplicaConvergence.fold lwwTotal (0, 0) [(2, 3), (1, 5), (1, 5)] := by
  decide

/-- The two concrete histories are different lists, so
    `lwwTotal_two_histories_converge` is not a trivial `rfl`. -/
example :
    ([(1, 5), (2, 3)] : List Write) ≠ [(2, 3), (1, 5), (1, 5)] := by decide

theorem lwwNaive_breaks_on_lwwTotal_histories :
    AutoproverCorpus.ReplicaConvergence.fold lwwNaive (0, 0) ([(1, 0), (1, 1)] : List Write) ≠
      AutoproverCorpus.ReplicaConvergence.fold lwwNaive (0, 0) [(1, 1), (1, 0)] := by
  decide

end AutoproverCorpus.LWWConvergence
