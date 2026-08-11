/-
  AutoproverCorpus.Concurrency.ResourceOrderingAcyclic

  Ordered resource acquisition makes the wait-for graph acyclic: acquiring resources in a fixed
  global order excludes circular wait. Safety only - the classical bridge from no-circular-wait
  to deadlock freedom is a disclosed textbook corollary, not proved here.

  Attribution: Classical (Havender, 1968; Coffman conditions, 1971).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Order.TransitiveClosure

namespace AutoproverCorpus.ResourceOrderingAcyclic

open AutoproverCorpus.TransitiveClosure (TC)

/-! ### (1) `rank` — a strict-upper-bound function on `List Nat` ("max resource held") -/

/-- A strict upper bound on every element of `l`: `1 +` the maximum element if `l` is
    nonempty, `0` if `l = []`. Only the two bounding lemmas below (`lt_rank_of_mem`,
    `rank_le_of_bound`) are used downstream — no "= max + 1" characterization is proved. -/
def rank (l : List Nat) : Nat := l.foldr (fun r acc => max (r + 1) acc) 0

/-- Every element of `l` is strictly below `rank l`. -/
theorem lt_rank_of_mem {l : List Nat} {r : Nat} (h : r ∈ l) : r < rank l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
      show r < max (x + 1) (rank xs)
      cases List.mem_cons.mp h with
      | inl heq =>
          have h1 := Nat.le_max_left (x + 1) (rank xs)
          omega
      | inr hmem =>
          have h1 := ih hmem
          have h2 := Nat.le_max_right (x + 1) (rank xs)
          omega

/-- If some `r` strictly exceeds every element of `l`, then `rank l ≤ r`. -/
theorem rank_le_of_bound {l : List Nat} {r : Nat} (h : ∀ r' ∈ l, r' < r) : rank l ≤ r := by
  induction l with
  | nil => exact Nat.zero_le r
  | cons x xs ih =>
      show max (x + 1) (rank xs) ≤ r
      have hx : x < r := h x List.mem_cons_self
      have hxs : rank xs ≤ r := ih (fun r' hr' => h r' (List.mem_cons_of_mem x hr'))
      exact Nat.max_le.mpr ⟨hx, hxs⟩

variable {Proc : Type}

/-! ### System state and the wait-for graph -/

/-- Snapshot of a resource-allocation system: for each process, the resources it currently
    HOLDS and the single resource it is currently WAITING for (`none` if not waiting). -/
structure SysState (Proc : Type) where
  holds : Proc → List Nat
  waits : Proc → Option Nat

def WaitEdge (st : SysState Proc) (pi pj : Proc) : Prop :=
  ∃ r, st.waits pi = some r ∧ r ∈ st.holds pj

abbrev Reach (st : SysState Proc) (pi pj : Proc) : Prop := TC (WaitEdge st) pi pj

/-- No circular wait: no process is reachable from itself along wait-for edges. -/
def Acyclic (st : SysState Proc) : Prop := ∀ p, ¬ Reach st p p

/-- Ordered acquisition (Havender/Dijkstra): a process may wait for a resource only if it is
    strictly greater, in the fixed global order on resources, than every resource it already
    holds. -/
def OrderedAcquisition (st : SysState Proc) : Prop :=
  ∀ pi r, st.waits pi = some r → ∀ r' ∈ st.holds pi, r' < r

/-- Each process's rank: `rank` applied to its held-resource list ("the max resource it
    holds", per (1)'s doc comment). -/
def procRank (st : SysState Proc) (p : Proc) : Nat := rank (st.holds p)

/-! ### (2)-(3) Ordered acquisition ⇒ every wait-for edge strictly increases rank -/

/-- Under ordered acquisition, a wait-for edge `Pi → Pj` strictly increases `procRank`. -/
theorem waitEdge_rank_lt {st : SysState Proc} (hord : OrderedAcquisition st) :
    ∀ {pi pj}, WaitEdge st pi pj → procRank st pi < procRank st pj := by
  rintro pi pj ⟨r, hwaits, hheld⟩
  have h1 : procRank st pi ≤ r := rank_le_of_bound (hord pi r hwaits)
  have h2 : r < procRank st pj := lt_rank_of_mem hheld
  omega

theorem reach_rank_lt {st : SysState Proc} (hord : OrderedAcquisition st)
    {pi pj : Proc} (h : Reach st pi pj) : procRank st pi < procRank st pj :=
  AutoproverCorpus.TransitiveClosure.tc_least
    (s := fun a b => procRank st a < procRank st b)
    (fun _x _y hxy => waitEdge_rank_lt hord hxy)
    (fun _ _ _ hxy hyz => Nat.lt_trans hxy hyz)
    h

/-! ### (4) The main theorem — safety only -/

/-- Ordered acquisition ⇒ the wait-for graph is `Acyclic`. A self-loop would force
    `procRank st p < procRank st p` by `reach_rank_lt`, impossible. -/
theorem orderedAcquisition_acyclic {st : SysState Proc} (hord : OrderedAcquisition st) :
    Acyclic st :=
  fun p hp => Nat.lt_irrefl (procRank st p) (reach_rank_lt hord hp)

theorem no_circular_wait {st : SysState Proc} (hord : OrderedAcquisition st) :
    ∀ p, ¬ Reach st p p :=
  orderedAcquisition_acyclic hord

/-! ### (5) Instance, positive: an ordered three-process chain -/

/-- Three processes in a wait-for chain `p1 → p2 → p3`. -/
inductive OrderedProc
  | p1 | p2 | p3

/-- `abbrev` so `decide` unfolds it on concrete arguments. -/
abbrev orderedHolds : OrderedProc → List Nat
  | .p1 => [1]
  | .p2 => [2]
  | .p3 => [3]

/-- `p1` holds `1` and waits for `2` (held by `p2`); `p2` holds `2` and waits for `3` (held by
    `p3`); `p3` holds `3` and waits for nothing. -/
abbrev orderedWaits : OrderedProc → Option Nat
  | .p1 => some 2
  | .p2 => some 3
  | .p3 => none

def orderedSt : SysState OrderedProc := { holds := orderedHolds, waits := orderedWaits }

/-- `orderedSt` genuinely satisfies ordered acquisition (concrete `decide`-backed bound
    checks, not assumed). -/
theorem orderedSt_ordered : OrderedAcquisition orderedSt := by
  intro pi r hr
  cases pi with
  | p1 =>
      simp only [orderedSt, orderedWaits, Option.some.injEq] at hr
      subst hr
      decide
  | p2 =>
      simp only [orderedSt, orderedWaits, Option.some.injEq] at hr
      subst hr
      decide
  | p3 =>
      simp [orderedSt, orderedWaits] at hr

/-- A REAL two-hop wait-for path (non-vacuous — `orderedSt` genuinely has wait-for edges),
    `decide`-backed at each hop. -/
theorem orderedSt_reach_p1_p3 : Reach orderedSt OrderedProc.p1 OrderedProc.p3 :=
  TC.trans (TC.base (show WaitEdge orderedSt OrderedProc.p1 OrderedProc.p2 from
              ⟨2, rfl, by decide⟩))
           (TC.base (show WaitEdge orderedSt OrderedProc.p2 OrderedProc.p3 from
              ⟨3, rfl, by decide⟩))

/-- Applying the main theorem: despite the genuine chain above, `orderedSt` is `Acyclic`. -/
example : Acyclic orderedSt := orderedAcquisition_acyclic orderedSt_ordered

/-! ### (6) Instance, negative — counterexample separating the hypotheses -/

/-- Two processes acquiring resources in OPPOSITE order. -/
inductive CyclicProc
  | q1 | q2

abbrev cyclicHolds : CyclicProc → List Nat
  | .q1 => [1]
  | .q2 => [2]

/-- `q1` holds `1`, waits for `2` (ordered: `2 > 1`). `q2` holds `2`, waits for `1` — this
    VIOLATES ordered acquisition (`1` is not `>` the `2` that `q2` already holds). -/
abbrev cyclicWaits : CyclicProc → Option Nat
  | .q1 => some 2
  | .q2 => some 1

def cyclicSt : SysState CyclicProc := { holds := cyclicHolds, waits := cyclicWaits }

/-- The two wait-for edges of the cycle, `decide`-backed. -/
theorem cyclicSt_edge_q1_q2 : WaitEdge cyclicSt CyclicProc.q1 CyclicProc.q2 :=
  ⟨2, rfl, by decide⟩

theorem cyclicSt_edge_q2_q1 : WaitEdge cyclicSt CyclicProc.q2 CyclicProc.q1 :=
  ⟨1, rfl, by decide⟩

/-- **A genuine, REACHABLE 2-cycle** — `cyclicSt` is NOT `Acyclic`. -/
theorem cyclicSt_not_acyclic : ¬ Acyclic cyclicSt := by
  intro hacyc
  exact hacyc CyclicProc.q1 (TC.trans (TC.base cyclicSt_edge_q1_q2) (TC.base cyclicSt_edge_q2_q1))

/-- **Why the cycle exists: `cyclicSt` genuinely violates ordered acquisition.** Applying the
    hypothesis at `q2` would force `2 < 1`. -/
theorem cyclicSt_not_ordered : ¬ OrderedAcquisition cyclicSt := by
  intro hord
  have h : (2 : Nat) < 1 := hord CyclicProc.q2 1 rfl 2 (by decide)
  omega

/-- **The general contrapositive of the main theorem** (`orderedAcquisition_acyclic` contraposed):
    for any state, a circular wait (a wait-for cycle) forces ordered acquisition to have failed.
    Universal name, universal statement. -/
theorem circular_wait_requires_unordered_acquisition {st : SysState Proc}
    (h : ¬ Acyclic st) : ¬ OrderedAcquisition st :=
  fun hord => h (orderedAcquisition_acyclic hord)

/-- **The essential cycle counterexample, packaged.** A concrete 2-cycle in the wait-for
    graph of `cyclicSt`, arising exactly because ordered acquisition fails — an instance
    for the general contrapositive above, showing its hypothesis is not decoration. -/
theorem cyclicSt_cycle_and_not_ordered :
    ¬ Acyclic cyclicSt ∧ ¬ OrderedAcquisition cyclicSt :=
  ⟨cyclicSt_not_acyclic, cyclicSt_not_ordered⟩

end AutoproverCorpus.ResourceOrderingAcyclic
