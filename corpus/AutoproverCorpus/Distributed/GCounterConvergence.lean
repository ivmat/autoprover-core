/-
  AutoproverCorpus.Distributed.GCounterConvergence

  G-Counter convergence: pointwise-max merge forms a join-semilattice (partial-order laws and
  least upper bound), increments are monotone, and replicas that have seen the same updates
  converge. Three-replica scope.

  Attribution: Classical (Shapiro, Preguica, Baquero and Zawirski, 2011).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Distributed.ReplicaConvergence

namespace AutoproverCorpus.GCounterConvergence

/-! ### The G-Counter state: a genuine multi-component vector (fixed at 3 replicas). -/

abbrev GState : Type := Nat × Nat × Nat

/-- Pointwise max merge, one `Nat.max` per component — the G-Counter's join operation. -/
def gmerge (a b : GState) : GState := (max a.1 b.1, max a.2.1 b.2.1, max a.2.2 b.2.2)

theorem gmerge_comm : AutoproverCorpus.ReplicaConvergence.Comm gmerge := by
  intro a b
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  unfold gmerge
  rw [Nat.max_comm a1 b1, Nat.max_comm a2 b2, Nat.max_comm a3 b3]

theorem gmerge_assoc : AutoproverCorpus.ReplicaConvergence.Assoc gmerge := by
  intro a b c
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨c1, c2, c3⟩ := c
  unfold gmerge
  rw [Nat.max_assoc a1 b1 c1, Nat.max_assoc a2 b2 c2, Nat.max_assoc a3 b3 c3]

theorem gmerge_idem : AutoproverCorpus.ReplicaConvergence.Idem gmerge := by
  intro a
  obtain ⟨a1, a2, a3⟩ := a
  unfold gmerge
  rw [Nat.max_self a1, Nat.max_self a2, Nat.max_self a3]

theorem gcounter_convergence (s : GState) {l1 l2 : List GState}
    (h : AutoproverCorpus.ReplicaConvergence.SameUpdates l1 l2) :
    AutoproverCorpus.ReplicaConvergence.fold gmerge s l1 = AutoproverCorpus.ReplicaConvergence.fold gmerge s l2 :=
  AutoproverCorpus.ReplicaConvergence.convergence gmerge_comm gmerge_assoc gmerge_idem s h

/-- The pointwise order on `GState`: the grow-only invariant order. -/
def GLe (a b : GState) : Prop := a.1 ≤ b.1 ∧ a.2.1 ≤ b.2.1 ∧ a.2.2 ≤ b.2.2

/-- `GLe` is reflexive — the first partial-order law (needed to legitimately call
    `(GState, GLe, gmerge)` a join-SEMILATTICE, not merely to exhibit upper bounds). -/
theorem GLe_refl (a : GState) : GLe a a := by
  obtain ⟨a1, a2, a3⟩ := a; exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- `GLe` is transitive. -/
theorem GLe_trans {a b c : GState} (hab : GLe a b) (hbc : GLe b c) : GLe a c := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b; obtain ⟨c1, c2, c3⟩ := c
  obtain ⟨p1, p2, p3⟩ := hab; obtain ⟨q1, q2, q3⟩ := hbc
  exact ⟨Nat.le_trans p1 q1, Nat.le_trans p2 q2, Nat.le_trans p3 q3⟩

/-- `GLe` is antisymmetric — the third partial-order law; with `GLe_refl`/`GLe_trans` this
    makes `GLe` a genuine partial order, so `gmerge` (its least upper bound) makes
    `(GState, GLe, gmerge)` a genuine join-semilattice. -/
theorem GLe_antisymm {a b : GState} (hab : GLe a b) (hba : GLe b a) : a = b := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨p1, p2, p3⟩ := hab; obtain ⟨q1, q2, q3⟩ := hba
  have e1 : a1 = b1 := Nat.le_antisymm p1 q1
  have e2 : a2 = b2 := Nat.le_antisymm p2 q2
  have e3 : a3 = b3 := Nat.le_antisymm p3 q3
  subst e1; subst e2; subst e3; rfl

/-- **Monotonicity of merge, left argument.** `merge` only grows a state: `a ≤ merge a
    b`, pointwise. The grow-only CRDT invariant, stated as a theorem. -/
theorem le_gmerge_left (a b : GState) : GLe a (gmerge a b) := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  unfold gmerge GLe
  exact ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _⟩

/-- **Monotonicity of merge, right argument.** Symmetric to `le_gmerge_left`. -/
theorem le_gmerge_right (a b : GState) : GLe b (gmerge a b) := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  unfold gmerge GLe
  exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _⟩

/-- **`merge` is the LEAST upper bound (join).** Together with `le_gmerge_left`/`_right`
    (which show `merge a b` is AN upper bound), this shows `merge a b` is the LEAST state
    above both `a` and `b` under `GLe` — `(GState, GLe, gmerge)` is a genuine
    join-semilattice, the structural fact `SameUpdates`-convergence rests on. -/
theorem gmerge_least_upper_bound (a b c : GState) (ha : GLe a c) (hb : GLe b c) :
    GLe (gmerge a b) c := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨c1, c2, c3⟩ := c
  simp only [GLe, gmerge] at ha hb ⊢
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨?_, ?_, ?_⟩ <;> omega

inductive ReplicaId
  | r0
  | r1
  | r2

/-- Bump the local component for replica `r` by one — the G-Counter's local update
    operation. -/
def increment (a : GState) : ReplicaId → GState
  | .r0 => (a.1 + 1, a.2.1, a.2.2)
  | .r1 => (a.1, a.2.1 + 1, a.2.2)
  | .r2 => (a.1, a.2.1, a.2.2 + 1)

/-- **Monotonicity of increment.** A local increment never decreases any component —
    the ONLY state-changing operation this model has (besides `merge`) preserves the
    grow-only invariant too. -/
theorem increment_monotone (a : GState) (r : ReplicaId) : GLe a (increment a r) := by
  obtain ⟨a1, a2, a3⟩ := a
  cases r <;> (simp only [GLe, increment]; omega)

/-- The G-Counter's externally observable value: the sum of its per-replica components. -/
def value (a : GState) : Nat := a.1 + a.2.1 + a.2.2

/-- The observable value never decreases under merge — a direct corollary of
    `le_gmerge_left`. -/
theorem value_le_value_gmerge (a b : GState) : value a ≤ value (gmerge a b) := by
  have h := le_gmerge_left a b
  unfold GLe at h
  unfold value
  omega

/-- The observable value never decreases under a local increment — a direct corollary
    of `increment_monotone`. -/
theorem value_increment_monotone (a : GState) (r : ReplicaId) :
    value a ≤ value (increment a r) := by
  have h := increment_monotone a r
  unfold GLe at h
  unfold value
  omega

/-! ### (3) Instance, and a counterexample separating `max` from `+` -/

/-- Instance: two different receive histories of the same conceptual
    update set — the plain order `[(1,0,0), (0,1,0), (0,0,1)]` versus the reordered
    history `[(0,0,1), (1,0,0), (0,1,0), (1,0,0)]`, which additionally redelivers replica
    0's update — converge to the same state `(1,1,1)` from genesis `(0,0,0)`, checked by
    `decide`. -/
theorem two_orders_converge :
    AutoproverCorpus.ReplicaConvergence.fold gmerge (0, 0, 0)
        [(1, 0, 0), (0, 1, 0), (0, 0, 1)] =
      AutoproverCorpus.ReplicaConvergence.fold gmerge (0, 0, 0)
        [(0, 0, 1), (1, 0, 0), (0, 1, 0), (1, 0, 0)] := by
  decide

/-- The two concrete histories above are different lists (not the same
    receive order), so `two_orders_converge` is not a trivial `rfl`. -/
example :
    ([(1, 0, 0), (0, 1, 0), (0, 0, 1)] : List GState) ≠
      [(0, 0, 1), (1, 0, 0), (0, 1, 0), (1, 0, 0)] := by
  decide

/-- Pointwise `+` — not a valid merge for a G-Counter, kept only to build the
    counterexample below. -/
def addMerge (a b : GState) : GState := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

/-- Counterexample (1 of 2): `addMerge` is not idempotent.
    Redelivering replica 0's own update to itself under pointwise `+` double-counts:
    `addMerge (1,0,0) (1,0,0) = (2,0,0) ≠ (1,0,0)`. This is exactly the failure `Idem`
    rules out, and exactly why `max`, not `+`, is the correct G-Counter merge. -/
theorem addMerge_not_idem : ¬ AutoproverCorpus.ReplicaConvergence.Idem addMerge := by
  intro h
  have heq := h (1, 0, 0)
  exact absurd heq (by decide)

/-- Counterexample (2 of 2): non-idempotence breaks convergence itself, not just
    the algebra. `[(1,0,0)]` and `[(1,0,0), (1,0,0)]` — one delivery of an update
    versus a redelivered duplicate — are `SameUpdates`-related (via the `dup`
    constructor). Under the correct merge `gmerge` they are guaranteed by
    `gcounter_convergence` to fold to the same state. Under `addMerge` they do not:
    folding reaches `(1,0,0)` versus `(2,0,0)`, a different state. This
    demonstrates that `+` double-counts on redelivery — motivating why the
    G-Counter's merge must be `max`, not `+`. -/
theorem addMerge_breaks_convergence :
    AutoproverCorpus.ReplicaConvergence.fold addMerge (0, 0, 0) [(1, 0, 0)] ≠
      AutoproverCorpus.ReplicaConvergence.fold addMerge (0, 0, 0) [(1, 0, 0), (1, 0, 0)] := by
  decide

end AutoproverCorpus.GCounterConvergence
