/-
  AutoproverCorpus.Order.FiniteAcyclicSink

  A finite nonempty acyclic directed graph has a sink: some node with no outgoing edge. Safety-
  only statement; no scheduling or liveness claim. Includes the corollary for acyclic wait-for
  graphs.

  Attribution: Classical (every finite nonempty DAG has a sink).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Concurrency.ResourceOrderingAcyclic
import AutoproverCorpus.Order.BoundedPath
import AutoproverCorpus.Distributed.QuorumIntersection

namespace AutoproverCorpus.FiniteAcyclicSink

open AutoproverCorpus.TransitiveClosure (TC)
open AutoproverCorpus.BoundedPath (Chain exists_dup_split)

/-! ### `Sink`, quantified within a finite carrier -/

abbrev Sink {Node : Type} (ps : List Node) (E : Node → Node → Prop) (p : Node) : Prop :=
  ∀ q ∈ ps, ¬ E p q

/-! ### Step 1: "no sink" builds an arbitrarily long `Chain` within `ps` -/

/-- If every process in `ps` has SOME outgoing edge back into `ps`, an `E`-chain of ANY
    length `n`, starting at any `p0 ∈ ps`, can be built entirely within `ps`. Plain
    structural recursion on `n`, consuming the per-process existential one step at a time. -/
theorem exists_chain_of_no_sink {Node : Type} {E : Node → Node → Prop} {ps : List Node}
    (hnosink : ∀ p ∈ ps, ∃ q ∈ ps, E p q) :
    ∀ (n : Nat) (p0 : Node), p0 ∈ ps →
      ∃ l : List Node, l.length = n ∧ Chain E p0 l ∧ ∀ x ∈ l, x ∈ ps
  | 0, _p0, _hp0 => ⟨[], rfl, trivial, fun x hx => by cases hx⟩
  | n + 1, p0, hp0 => by
      obtain ⟨q, hq, hEq⟩ := hnosink p0 hp0
      obtain ⟨l, hlen, hchain, hmem⟩ := exists_chain_of_no_sink hnosink n q hq
      refine ⟨q :: l, by rw [List.length_cons, hlen], ⟨hEq, hchain⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hq
      · exact hmem x hx'

/-! ### Step 2: walking a `Chain` reaches every node it lists, not just the last -/

theorem chain_reaches_mem {Node : Type} {r : Node → Node → Prop} :
    ∀ {prev : Node} {l : List Node}, Chain r prev l → ∀ y ∈ l, TC r prev y
  | _prev, [], _hchain, _y, hy => by cases hy
  | prev, a :: t, hchain, y, hy => by
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact TC.base hchain.1
      · exact TC.trans (TC.base hchain.1) (chain_reaches_mem hchain.2 y hy')

/-! ### Step 3: a repeated node in a `Chain` yields a genuine cycle through it -/

theorem chain_cycle_of_dup {Node : Type} {r : Node → Node → Prop} {x : Node} :
    ∀ {prev : Node} (l1 l2 l3 : List Node),
      Chain r prev (l1 ++ x :: l2 ++ x :: l3) → TC r x x
  | _prev, [], l2, _l3, h =>
      chain_reaches_mem h.2 x (List.mem_append_right l2 List.mem_cons_self)
  | _prev, _y :: l1', l2, l3, h => chain_cycle_of_dup l1' l2 l3 h.2

/-! ### Step 4: THE MAIN THEOREM — general graph fact, abstract edge relation -/

theorem finite_acyclic_has_sink {Node : Type} [DecidableEq Node]
    (E : Node → Node → Prop) (ps : List Node) (hne : ps ≠ [])
    (hacyc : ∀ p, ¬ TC E p p) :
    ∃ p ∈ ps, Sink ps E p := by
  apply Classical.byContradiction
  intro hno
  have hnosink : ∀ p ∈ ps, ∃ q ∈ ps, E p q := by
    intro p hp
    apply Classical.byContradiction
    intro hc
    exact hno ⟨p, hp, fun q hq hEq => hc ⟨q, hq, hEq⟩⟩
  obtain ⟨p0, rest, hps⟩ : ∃ p0 rest, ps = p0 :: rest := by
    cases ps with
    | nil => exact absurd rfl hne
    | cons p0 rest => exact ⟨p0, rest, rfl⟩
  have hp0 : p0 ∈ ps := by rw [hps]; exact List.mem_cons_self
  obtain ⟨l, hlen, hchain, hmem⟩ :=
    exists_chain_of_no_sink hnosink (ps.length + 1) p0 hp0
  have hlsub : l ⊆ ps := fun a ha => hmem a ha
  have hnnodup : ¬ l.Nodup := by
    intro hnodup
    have hle := AutoproverCorpus.QuorumIntersection.length_le_of_subset_of_nodup hnodup hlsub
    rw [hlen] at hle
    omega
  obtain ⟨x, l1, l2, l3, hsplit⟩ := exists_dup_split l hnnodup
  rw [hsplit] at hchain
  exact hacyc x (chain_cycle_of_dup l1 l2 l3 hchain)

theorem waitfor_finite_acyclic_has_sink {Proc : Type} [DecidableEq Proc]
    (st : AutoproverCorpus.ResourceOrderingAcyclic.SysState Proc) (ps : List Proc) (hne : ps ≠ [])
    (hacyc : AutoproverCorpus.ResourceOrderingAcyclic.Acyclic st) :
    ∃ p ∈ ps, Sink ps (AutoproverCorpus.ResourceOrderingAcyclic.WaitEdge st) p :=
  finite_acyclic_has_sink (AutoproverCorpus.ResourceOrderingAcyclic.WaitEdge st) ps hne hacyc

/-! ### Sharpness: finiteness is essential, proved (not merely asserted) -/

section NatSuccCounterexample

/-- The successor relation on `Nat`: `n` "waits for" `n + 1`. Demonstrates that dropping the
    finite-carrier hypothesis makes `finite_acyclic_has_sink` false: `succEdge` is
    `Acyclic` (`succEdge_acyclic`) yet has no sink anywhere in `Nat` (`succEdge_no_sink`) —
    every `n` has an outgoing edge to `n + 1`. -/
def succEdge (n m : Nat) : Prop := m = n + 1

theorem succEdge_lt {n m : Nat} (h : TC succEdge n m) : n < m := by
  induction h with
  | base hnm => simp only [succEdge] at hnm; omega
  | trans _ _ ihab ihbc => omega

/-- `succEdge` is `Acyclic`: a self-loop would force `p < p`. -/
theorem succEdge_acyclic : ∀ p : Nat, ¬ TC succEdge p p :=
  fun p h => absurd (succEdge_lt h) (Nat.lt_irrefl p)

/-- **Sharpness: finiteness is essential.** No sink exists anywhere in `Nat` for
    `succEdge`, despite it being `Acyclic` — every `n` has an outgoing edge to `n + 1`.
    Without a finite carrier hypothesis, `finite_acyclic_has_sink` would be false; this is
    the counterexample, proved rather than merely asserted. -/
theorem succEdge_no_sink : ¬ ∃ n : Nat, ∀ m, ¬ succEdge n m :=
  fun ⟨n, hn⟩ => hn (n + 1) rfl

end NatSuccCounterexample

/-! ### Instances: both hypotheses of the main theorem shown to be essential, concretely -/

section Instances

open AutoproverCorpus.ResourceOrderingAcyclic

-- `finite_acyclic_has_sink`/`waitfor_finite_acyclic_has_sink` general theorem's
-- `[DecidableEq Node]` hypothesis (needed for `exists_dup_split`'s pigeonhole splitting)
-- must be discharged when applying it to `orderedSt`'s carrier `OrderedProc`, which has
-- only three constructors and no field data.
deriving instance DecidableEq for OrderedProc

theorem orderedSt_p3_sink :
    Sink [OrderedProc.p1, OrderedProc.p2, OrderedProc.p3] (WaitEdge orderedSt)
      OrderedProc.p3 := by
  rintro q - ⟨r, hr, -⟩
  simp [orderedSt, orderedWaits] at hr

/-- The general theorem, exercised on `orderedSt`'s own carrier: a sink exists, per
    `finite_acyclic_has_sink`/`waitfor_finite_acyclic_has_sink`, not merely asserted by the
    concrete witness above. -/
example :
    ∃ p ∈ [OrderedProc.p1, OrderedProc.p2, OrderedProc.p3],
      Sink [OrderedProc.p1, OrderedProc.p2, OrderedProc.p3] (WaitEdge orderedSt) p :=
  waitfor_finite_acyclic_has_sink orderedSt [OrderedProc.p1, OrderedProc.p2, OrderedProc.p3]
    (by simp) (orderedAcquisition_acyclic orderedSt_ordered)

theorem cyclicSt_no_sink :
    ¬ ∃ p ∈ [CyclicProc.q1, CyclicProc.q2],
        Sink [CyclicProc.q1, CyclicProc.q2] (WaitEdge cyclicSt) p := by
  rintro ⟨p, -, hsink⟩
  cases p with
  | q1 => exact hsink CyclicProc.q2 (by simp) cyclicSt_edge_q1_q2
  | q2 => exact hsink CyclicProc.q1 (by simp) cyclicSt_edge_q2_q1

end Instances

end AutoproverCorpus.FiniteAcyclicSink
