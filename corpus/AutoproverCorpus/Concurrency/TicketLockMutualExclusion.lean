/-
  AutoproverCorpus.Concurrency.TicketLockMutualExclusion

  The ticket lock guarantees mutual exclusion, for an ARBITRARY number of threads. A thread
  takes a ticket by fetch-and-increment on `next`, spins until the `serving` counter reaches its
  ticket, and on leaving the critical section increments `serving`. The proof is an inductive
  invariant over an explicit state machine — three clauses, of which the load-bearing one is
  that live tickets are pairwise DISTINCT — carried over reachable states by induction:

    * `servingLeNext`  : `serving ≤ next`;
    * `ticketRange`    : every live ticket `t` satisfies `serving ≤ t < next`;
    * `ticketsDistinct`: two threads holding the same ticket are the same thread;
    * `inCSserving`    : a thread in the critical section holds exactly the ticket now served.

  Mutual exclusion is then immediate: two threads in the critical section both hold the ticket
  `serving`, and distinctness collapses them to one thread. Note where the work is — the `leave`
  case, which increments `serving` and must re-establish `serving ≤ t` for every OTHER live
  ticket; that step needs distinctness, which is why the invariant cannot be weakened to the
  range clause alone.

  Unlike this corpus's `DekkerMutex` and `PetersonMutex` — two-thread algorithms whose invariants
  are closed by `decide` over a finite state space — the state space here is infinite (ticket
  counters are unbounded `Nat`s) and the thread type is an arbitrary type, so the argument is a
  genuine induction rather than a finite check.

  SCOPE (safety only, and one modelling assumption stated plainly):
    * MUTUAL EXCLUSION only. The ticket lock's other classical selling point — FIFO fairness,
      hence no starvation and bounded waiting — is NOT proved here, nor is deadlock-freedom or
      any progress property.
    * Fetch-and-increment is modelled as a SINGLE atomic step (`takeTicket`). The hardware
      atomicity that real implementations rely on is an assumption of the model, not a theorem;
      a non-atomic ticket acquisition would break the distinctness clause and with it the proof.

  Attribution: Classical (the ticket lock; P. J. Courtois-era sequencers formalized in D. P. Reed
  and R. K. Kanodia, "Synchronization with Eventcounts and Sequencers", CACM, 1979; analysed in
  J. M. Mellor-Crummey and M. L. Scott, ACM TOCS, 1991). Its ancestor is L. Lamport's bakery
  algorithm, 1974.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.TicketLockMutualExclusion

/-! ### The state machine -/

/-- A thread's control state: not competing; holding ticket `t` and spinning; or holding ticket
    `t` inside the critical section. -/
inductive Phase where
  | idle
  | waiting (t : Nat)
  | inCS (t : Nat)
  deriving DecidableEq, Repr

/-- The ticket a thread currently holds, if any. A thread holds the SAME ticket while spinning
    and while in the critical section — it is released only on leaving. -/
def ticketOf : Phase → Option Nat
  | .idle => none
  | .waiting t => some t
  | .inCS t => some t

/-- Global state: the next ticket to hand out, the ticket currently being served, and each
    thread's phase. -/
structure TState (Thread : Type) where
  next : Nat
  serving : Nat
  phase : Thread → Phase

/-- The initial state: no tickets handed out, counter at zero, every thread idle. -/
def initState (Thread : Type) : TState Thread :=
  { next := 0, serving := 0, phase := fun _ => Phase.idle }

/-- A thread in the critical section holds a live ticket — the bridge from the `phase` clause to
    the `ticketOf` clauses. -/
theorem ticketOf_inCS {Thread : Type} {s : TState Thread} {i : Thread} {t : Nat}
    (h : s.phase i = Phase.inCS t) : ticketOf (s.phase i) = some t := by rw [h]; rfl

section Model

variable {Thread : Type} [DecidableEq Thread]

/-- The three transitions of the ticket lock. -/
inductive Step : TState Thread → TState Thread → Prop where
  /-- **Fetch-and-increment.** An idle thread takes the current `next` as its ticket and
      increments `next`, atomically (see the scope note in the header). -/
  | takeTicket {s : TState Thread} (i : Thread) (hidle : s.phase i = Phase.idle) :
      Step s { s with
        next := s.next + 1
        phase := fun j => if j = i then Phase.waiting s.next else s.phase j }
  /-- **Acquire.** A spinning thread whose ticket is the one being served enters the critical
      section. This is the only guard in the algorithm. -/
  | enter {s : TState Thread} (i : Thread) (t : Nat)
      (hwait : s.phase i = Phase.waiting t) (hserved : t = s.serving) :
      Step s { s with phase := fun j => if j = i then Phase.inCS t else s.phase j }
  /-- **Release.** The thread in the critical section leaves and increments `serving`. -/
  | leave {s : TState Thread} (i : Thread) (t : Nat) (hcs : s.phase i = Phase.inCS t) :
      Step s { s with
        serving := s.serving + 1
        phase := fun j => if j = i then Phase.idle else s.phase j }

/-- Reachability: the reflexive-transitive closure of `Step`, rooted at `initState`. -/
inductive Reachable : TState Thread → Prop where
  | init : Reachable (initState Thread)
  | step {s s' : TState Thread} (hr : Reachable s) (hst : Step s s') : Reachable s'

/-! ### The inductive invariant -/

/-- The invariant carried over reachable states; see the header for the role of each clause. -/
structure Inv (s : TState Thread) : Prop where
  servingLeNext : s.serving ≤ s.next
  ticketRange : ∀ i t, ticketOf (s.phase i) = some t → s.serving ≤ t ∧ t < s.next
  ticketsDistinct : ∀ i j t, ticketOf (s.phase i) = some t → ticketOf (s.phase j) = some t → i = j
  inCSserving : ∀ i t, s.phase i = Phase.inCS t → t = s.serving

/-- **The reachability induction.** Every reachable state satisfies `Inv`. The `init` case is
    immediate (no live tickets); each step case is a per-clause check, with the `leave` case
    carrying the argument described in the header. -/
theorem invariant_holds {s : TState Thread} (h : Reachable s) : Inv s := by
  induction h with
  | init =>
    refine ⟨Nat.le_refl 0, ?_, ?_, ?_⟩
    · intro i t hi; simp [initState, ticketOf] at hi
    · intro i j t hi _; simp [initState, ticketOf] at hi
    · intro i t hi; simp [initState] at hi
  | @step s0 _s1 _hr hst ih =>
    cases hst with
    | takeTicket i hidle =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · show s0.serving ≤ s0.next + 1
        have := ih.servingLeNext
        omega
      · intro j t hj
        show s0.serving ≤ t ∧ t < s0.next + 1
        dsimp only at hj
        by_cases hji : j = i
        · rw [if_pos hji] at hj
          have ht : s0.next = t := by simpa [ticketOf] using hj
          have := ih.servingLeNext
          omega
        · rw [if_neg hji] at hj
          have := ih.ticketRange j t hj
          omega
      · intro j k t hj hk
        dsimp only at hj hk
        by_cases hji : j = i <;> by_cases hki : k = i
        · rw [hji, hki]
        · rw [if_pos hji] at hj
          rw [if_neg hki] at hk
          have ht : s0.next = t := by simpa [ticketOf] using hj
          have := (ih.ticketRange k t hk).2
          omega
        · rw [if_neg hji] at hj
          rw [if_pos hki] at hk
          have ht : s0.next = t := by simpa [ticketOf] using hk
          have := (ih.ticketRange j t hj).2
          omega
        · rw [if_neg hji] at hj
          rw [if_neg hki] at hk
          exact ih.ticketsDistinct j k t hj hk
      · intro j t hj
        show t = s0.serving
        dsimp only at hj
        by_cases hji : j = i
        · rw [if_pos hji] at hj; exact absurd hj (by simp)
        · rw [if_neg hji] at hj; exact ih.inCSserving j t hj
    | enter i t hwait hserved =>
      -- Entering changes no ticket: the thread keeps the ticket it was spinning on, so the
      -- range and distinctness clauses transfer unchanged.
      have hsame : ∀ j : Thread,
          ticketOf (if j = i then Phase.inCS t else s0.phase j) = ticketOf (s0.phase j) := by
        intro j
        by_cases hji : j = i
        · rw [if_pos hji, hji, hwait]; rfl
        · rw [if_neg hji]
      refine ⟨ih.servingLeNext, ?_, ?_, ?_⟩
      · intro j u hj
        dsimp only at hj
        rw [hsame j] at hj
        exact ih.ticketRange j u hj
      · intro j k u hj hk
        dsimp only at hj hk
        rw [hsame j] at hj
        rw [hsame k] at hk
        exact ih.ticketsDistinct j k u hj hk
      · intro j u hj
        show u = s0.serving
        dsimp only at hj
        by_cases hji : j = i
        · rw [if_pos hji] at hj
          have hut : t = u := by simpa using hj
          rw [← hut]
          exact hserved
        · rw [if_neg hji] at hj
          exact ih.inCSserving j u hj
    | leave i t hcs =>
      have hticket := ticketOf_inCS hcs
      have hserv := ih.inCSserving i t hcs
      have hlt := (ih.ticketRange i t hticket).2
      -- The load-bearing step: every OTHER live ticket differs from the one just released, so
      -- incrementing `serving` past it keeps `serving ≤ ticket` for all remaining threads.
      have hother : ∀ j u, j ≠ i → ticketOf (s0.phase j) = some u → s0.serving + 1 ≤ u := by
        intro j u hji hj
        have hge := (ih.ticketRange j u hj).1
        have hne : u ≠ t := by
          intro hu
          apply hji
          refine ih.ticketsDistinct j i t ?_ hticket
          rw [← hu]; exact hj
        omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · show s0.serving + 1 ≤ s0.next
        omega
      · intro j u hj
        show s0.serving + 1 ≤ u ∧ u < s0.next
        dsimp only at hj
        by_cases hji : j = i
        · rw [if_pos hji] at hj; simp [ticketOf] at hj
        · rw [if_neg hji] at hj
          exact ⟨hother j u hji hj, (ih.ticketRange j u hj).2⟩
      · intro j k u hj hk
        dsimp only at hj hk
        by_cases hji : j = i
        · rw [if_pos hji] at hj; simp [ticketOf] at hj
        · by_cases hki : k = i
          · rw [if_pos hki] at hk; simp [ticketOf] at hk
          · rw [if_neg hji] at hj
            rw [if_neg hki] at hk
            exact ih.ticketsDistinct j k u hj hk
      · intro j u hj
        dsimp only at hj
        by_cases hji : j = i
        · rw [if_pos hji] at hj; exact absurd hj (by simp)
        · rw [if_neg hji] at hj
          -- A second thread in the critical section would hold the released ticket too.
          exfalso
          have hu := ih.inCSserving j u hj
          have hjt : ticketOf (s0.phase j) = some t := by
            rw [hj]
            show some u = some t
            rw [hu, hserv]
          exact hji (ih.ticketsDistinct j i t hjt hticket)

/-! ### Mutual exclusion -/

/-- **Mutual exclusion (main theorem).** In any reachable state, two threads in the critical
    section are the same thread. Both hold the ticket currently being served (`inCSserving`), and
    two holders of one ticket coincide (`ticketsDistinct`). Stated for an arbitrary thread type:
    no bound on the number of threads. -/
theorem mutual_exclusion {s : TState Thread} (h : Reachable s) {i j : Thread} {t u : Nat}
    (hi : s.phase i = Phase.inCS t) (hj : s.phase j = Phase.inCS u) : i = j := by
  have inv := invariant_holds h
  have ht : t = s.serving := inv.inCSserving i t hi
  have hu : u = s.serving := inv.inCSserving j u hj
  refine inv.ticketsDistinct i j t (ticketOf_inCS hi) ?_
  rw [hj, hu, ht]
  rfl

/-- The contrapositive, in the form an operator states it: two DISTINCT threads are never in the
    critical section at the same time. -/
theorem no_two_distinct_in_cs {s : TState Thread} (h : Reachable s) {i j : Thread}
    (hij : i ≠ j) : ¬ (∃ t u, s.phase i = Phase.inCS t ∧ s.phase j = Phase.inCS u) := by
  rintro ⟨t, u, hi, hj⟩
  exact hij (mutual_exclusion h hi hj)

/-- Corollary of the invariant, worth stating on its own: the ticket held inside the critical
    section is exactly the one being served — the lock's guard is what it claims to be. -/
theorem inCS_holds_served_ticket {s : TState Thread} (h : Reachable s) {i : Thread} {t : Nat}
    (hi : s.phase i = Phase.inCS t) : t = s.serving :=
  (invariant_holds h).inCSserving i t hi

end Model

/-! ### Non-vacuity: a reachable state with one thread inside and another waiting -/

/-- Two threads. -/
inductive Two where
  | a | b
  deriving DecidableEq, Repr

/-- **The theorem is not vacuous.** A concrete three-step execution — `a` takes ticket 0, `b`
    takes ticket 1, `a` enters — reaches a state in which `a` IS in the critical section while
    `b` genuinely waits. So `mutual_exclusion` is not true merely because no reachable state
    ever has a thread inside the critical section. -/
theorem reachable_cs_with_waiter :
    ∃ s : TState Two, Reachable s ∧ s.phase Two.a = Phase.inCS 0 ∧
      s.phase Two.b = Phase.waiting 1 := by
  have h1 := Reachable.step (Reachable.init (Thread := Two)) (Step.takeTicket Two.a rfl)
  have h2 := Reachable.step h1 (Step.takeTicket Two.b (by decide))
  have h3 := Reachable.step h2 (Step.enter Two.a 0 (by decide) rfl)
  exact ⟨_, h3, by decide, by decide⟩

/-- And in that state, mutual exclusion says what it should: `b`, which is waiting, is not in the
    critical section, and no second thread can be. -/
example : ∀ s : TState Two, Reachable s → Two.a ≠ Two.b →
    ¬ (∃ t u, s.phase Two.a = Phase.inCS t ∧ s.phase Two.b = Phase.inCS u) :=
  fun _s h hne => no_two_distinct_in_cs h hne

end AutoproverCorpus.TicketLockMutualExclusion
