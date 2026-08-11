/-
  AutoproverCorpus.Distributed.PNCounterConvergence

  PN-Counter convergence: state is a pair of G-Counters merged pointwise; replicas seeing the
  same updates converge, while the observable value P - N is NOT monotone (a decrement lowers
  it) even though the state is grow-only. Convergence means inter-replica agreement, not
  monotone growth.

  Attribution: Classical (Shapiro, Preguica, Baquero and Zawirski, 2011).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Distributed.GCounterConvergence
import AutoproverCorpus.Distributed.ReplicaConvergence

namespace AutoproverCorpus.PNCounterConvergence

abbrev PNState : Type := AutoproverCorpus.GCounterConvergence.GState × AutoproverCorpus.GCounterConvergence.GState

def pnMerge (a b : PNState) : PNState :=
  (AutoproverCorpus.GCounterConvergence.gmerge a.1 b.1, AutoproverCorpus.GCounterConvergence.gmerge a.2 b.2)

theorem pnMerge_comm : AutoproverCorpus.ReplicaConvergence.Comm pnMerge := by
  intro a b
  obtain ⟨aP, aN⟩ := a
  obtain ⟨bP, bN⟩ := b
  unfold pnMerge
  rw [AutoproverCorpus.GCounterConvergence.gmerge_comm aP bP,
    AutoproverCorpus.GCounterConvergence.gmerge_comm aN bN]

theorem pnMerge_assoc : AutoproverCorpus.ReplicaConvergence.Assoc pnMerge := by
  intro a b c
  obtain ⟨aP, aN⟩ := a
  obtain ⟨bP, bN⟩ := b
  obtain ⟨cP, cN⟩ := c
  unfold pnMerge
  rw [AutoproverCorpus.GCounterConvergence.gmerge_assoc aP bP cP,
    AutoproverCorpus.GCounterConvergence.gmerge_assoc aN bN cN]

theorem pnMerge_idem : AutoproverCorpus.ReplicaConvergence.Idem pnMerge := by
  intro a
  obtain ⟨aP, aN⟩ := a
  unfold pnMerge
  rw [AutoproverCorpus.GCounterConvergence.gmerge_idem aP, AutoproverCorpus.GCounterConvergence.gmerge_idem aN]

theorem pncounter_convergence (s : PNState) {l1 l2 : List PNState}
    (h : AutoproverCorpus.ReplicaConvergence.SameUpdates l1 l2) :
    AutoproverCorpus.ReplicaConvergence.fold pnMerge s l1 = AutoproverCorpus.ReplicaConvergence.fold pnMerge s l2 :=
  AutoproverCorpus.ReplicaConvergence.convergence pnMerge_comm pnMerge_assoc pnMerge_idem s h

/-! ### (B) The state grows monotonically — the join-semilattice invariant on the pair. -/

/-- The pointwise order on `PNState`: both the P and N G-Counters must be pointwise `≤`. -/
def PNLe (a b : PNState) : Prop :=
  AutoproverCorpus.GCounterConvergence.GLe a.1 b.1 ∧ AutoproverCorpus.GCounterConvergence.GLe a.2 b.2

/-- **Monotonicity of `pnMerge`, left argument.** `pnMerge` only grows the pair-state. -/
theorem le_pnMerge_left (a b : PNState) : PNLe a (pnMerge a b) := by
  obtain ⟨aP, aN⟩ := a
  obtain ⟨bP, bN⟩ := b
  unfold pnMerge PNLe
  exact ⟨AutoproverCorpus.GCounterConvergence.le_gmerge_left aP bP,
    AutoproverCorpus.GCounterConvergence.le_gmerge_left aN bN⟩

/-- **Monotonicity of `pnMerge`, right argument.** Symmetric to `le_pnMerge_left`. -/
theorem le_pnMerge_right (a b : PNState) : PNLe b (pnMerge a b) := by
  obtain ⟨aP, aN⟩ := a
  obtain ⟨bP, bN⟩ := b
  unfold pnMerge PNLe
  exact ⟨AutoproverCorpus.GCounterConvergence.le_gmerge_right aP bP,
    AutoproverCorpus.GCounterConvergence.le_gmerge_right aN bN⟩

/-- Bump the P (increment) G-Counter at replica `r`; N is untouched. -/
def inc (a : PNState) (r : AutoproverCorpus.GCounterConvergence.ReplicaId) : PNState :=
  (AutoproverCorpus.GCounterConvergence.increment a.1 r, a.2)

/-- Bump the N (decrement) G-Counter at replica `r`; P is untouched. -/
def dec (a : PNState) (r : AutoproverCorpus.GCounterConvergence.ReplicaId) : PNState :=
  (a.1, AutoproverCorpus.GCounterConvergence.increment a.2 r)

/-- **`inc` grows the pair-state.** Bumping P never lowers either component. -/
theorem inc_grows (a : PNState) (r : AutoproverCorpus.GCounterConvergence.ReplicaId) :
    PNLe a (inc a r) := by
  obtain ⟨aP, aN⟩ := a
  unfold inc PNLe
  exact ⟨AutoproverCorpus.GCounterConvergence.increment_monotone aP r,
    AutoproverCorpus.GCounterConvergence.GLe_refl aN⟩

/-- **`dec` ALSO grows the pair-state.** This is the crux of the paradox: bumping N — the
    operation that LOWERS the observable value, per (C) — never lowers the STATE. Both
    G-Counters inside a PN-Counter are grow-only; only the DERIVED value can fall. -/
theorem dec_grows (a : PNState) (r : AutoproverCorpus.GCounterConvergence.ReplicaId) :
    PNLe a (dec a r) := by
  obtain ⟨aP, aN⟩ := a
  unfold dec PNLe
  exact ⟨AutoproverCorpus.GCounterConvergence.GLe_refl aP,
    AutoproverCorpus.GCounterConvergence.increment_monotone aN r⟩

/-! ### The observable value: `Int`, not `Nat` — it goes negative and it decreases. -/

/-- The PN-Counter's externally observable reading: `P`'s total minus `N`'s total. Must
    be `Int` — a `Nat` reading would truncate at 0 and hide exactly the
    non-monotonicity (C) exists to state. -/
def value (a : PNState) : Int :=
  (AutoproverCorpus.GCounterConvergence.value a.1 : Int) - (AutoproverCorpus.GCounterConvergence.value a.2 : Int)

/-! ### (C) THE REFUTATION — value is NON-monotone under `dec`. -/

/-- The concrete witness: `P = (1,0,0)`, `N = (0,0,0)`, so `value witnessA = 1`. -/
def witnessA : PNState := ((1, 0, 0), (0, 0, 0))

/-- `value witnessA = 1`, checked concretely. -/
theorem witnessA_value : value witnessA = 1 := by decide

/-- **The concrete decrement witness.** `dec witnessA .r0` STRICTLY LOWERS the value —
    from `1` to `0` — even though (per `dec_grows`) the underlying STATE only grew. This
    is the falsifying instance for `value_not_monotone` below. -/
theorem dec_strictly_decreases_value :
    value (dec witnessA .r0) < value witnessA := by decide

/-- The state grows under this same `dec` step (an instance of `dec_grows`), stated
    alongside `dec_strictly_decreases_value` to make the paradox explicit at a single
    concrete witness: STATE grows, VALUE falls. -/
theorem dec_grows_witnessA : PNLe witnessA (dec witnessA .r0) := dec_grows witnessA .r0

/-- **THE REFUTATION, stated generally.** The "value grows" reading of a PN-Counter is
    FALSE: it is NOT the case that every `dec` step leaves the value no smaller. Refuted
    by the concrete witness `witnessA`/`dec_strictly_decreases_value`, not weakened into
    a true-but-different statement. -/
theorem value_not_monotone : ¬ (∀ a r, value a ≤ value (dec a r)) := by
  intro h
  exact absurd (h witnessA .r0) (by decide)

/-! ### (D) Value still CONVERGES — agreement, not growth. -/

/-- **VALUE AGREEMENT.** Because `value` is a function of the state, (A)'s state-level
    convergence gives value-level agreement for free: two replicas whose histories are
    `SameUpdates`-related fold to states with the SAME observable value — even though
    (C) shows that value is not monotone as updates accrue. This is the precise sense in
    which "the PN-Counter converges": AGREEMENT across replicas, not monotone growth of
    the observable. -/
theorem pnvalue_agrees_of_sameUpdates (s : PNState) {l1 l2 : List PNState}
    (h : AutoproverCorpus.ReplicaConvergence.SameUpdates l1 l2) :
    value (AutoproverCorpus.ReplicaConvergence.fold pnMerge s l1) =
      value (AutoproverCorpus.ReplicaConvergence.fold pnMerge s l2) :=
  congrArg value (pncounter_convergence s h)

/-! ### (E) Counterexample separating the hypotheses: a reorder plus a redelivered `dec`. -/

theorem two_orders_converge :
    AutoproverCorpus.ReplicaConvergence.fold pnMerge ((0, 0, 0), (0, 0, 0))
        [((1, 0, 0), (0, 0, 0)), ((0, 1, 0), (0, 0, 0)), ((0, 0, 0), (0, 0, 1))] =
      AutoproverCorpus.ReplicaConvergence.fold pnMerge ((0, 0, 0), (0, 0, 0))
        [((0, 0, 0), (0, 0, 1)), ((1, 0, 0), (0, 0, 0)), ((0, 1, 0), (0, 0, 0)),
          ((0, 0, 0), (0, 0, 1))] := by
  decide

/-- The two concrete histories above are genuinely different lists (not the same receive
    order), so `two_orders_converge` is not a vacuous `rfl`. -/
example :
    ([((1, 0, 0), (0, 0, 0)), ((0, 1, 0), (0, 0, 0)), ((0, 0, 0), (0, 0, 1))] : List PNState) ≠
      [((0, 0, 0), (0, 0, 1)), ((1, 0, 0), (0, 0, 0)), ((0, 1, 0), (0, 0, 0)),
        ((0, 0, 0), (0, 0, 1))] := by
  decide

/-- **VALUE agreement at the same concrete witness.** The two histories above also fold
    to the SAME `value` (`1`), a direct corollary of `two_orders_converge` pushed through
    `value` — the concrete instance of (D)'s general fact `pnvalue_agrees_of_sameUpdates`. -/
theorem two_orders_converge_value :
    value (AutoproverCorpus.ReplicaConvergence.fold pnMerge ((0, 0, 0), (0, 0, 0))
        [((1, 0, 0), (0, 0, 0)), ((0, 1, 0), (0, 0, 0)), ((0, 0, 0), (0, 0, 1))]) =
      value (AutoproverCorpus.ReplicaConvergence.fold pnMerge ((0, 0, 0), (0, 0, 0))
        [((0, 0, 0), (0, 0, 1)), ((1, 0, 0), (0, 0, 0)), ((0, 1, 0), (0, 0, 0)),
          ((0, 0, 0), (0, 0, 1))]) :=
  congrArg value two_orders_converge

end AutoproverCorpus.PNCounterConvergence
