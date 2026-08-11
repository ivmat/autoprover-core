/-
  AutoproverCorpus.Processes.Diagnosability

  Diagnosability of discrete-event systems over a finite automaton with observable and
  unobservable events, with one diagnosable and one non-2-diagnosable worked automaton. The
  unbounded (for-all-N) negative result is proved separately (see DiagnosabilityUnbounded).

  Attribution: Classical (Sampath et al., 1995).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.Diagnosability

variable {State Event : Type}

/-! ### The DES model -/

/-- `es` is an event sequence taking `s` to `s'` under `step`. -/
inductive Reach (step : State → Event → State → Prop) : State → List Event → State → Prop where
  | nil (s : State) : Reach step s [] s
  | cons {s s' s'' : State} {e : Event} {es : List Event}
      (h1 : step s e s') (h2 : Reach step s' es s'') : Reach step s (e :: es) s''

/-- `es` is a run of the system: a finite event sequence performable from `init`. -/
def Run (step : State → Event → State → Prop) (init : State) (es : List Event) : Prop :=
  ∃ s, Reach step init es s

/-- Erase the unobservable events. -/
def proj (observable : Event → Bool) (es : List Event) : List Event :=
  es.filter observable

/-! ### (a) `proj` basics -/

theorem proj_append (observable : Event → Bool) (l1 l2 : List Event) :
    proj observable (l1 ++ l2) = proj observable l1 ++ proj observable l2 := by
  simp [proj, List.filter_append]

theorem proj_idem (observable : Event → Bool) (es : List Event) :
    proj observable (proj observable es) = proj observable es := by
  simp [proj, List.filter_filter, Bool.and_self]

theorem proj_mem_iff (observable : Event → Bool) (es : List Event) (e : Event) :
    e ∈ proj observable es ↔ e ∈ es ∧ observable e = true := by
  simp [proj, List.mem_filter]

/-! ### Fault predicates -/

/-- `es` contains a fault event with at least `N` further events after it. -/
def FaultThenN (isFault : Event → Bool) (N : Nat) (es : List Event) : Prop :=
  ∃ pre e suf, es = pre ++ e :: suf ∧ isFault e = true ∧ N ≤ suf.length

/-- No event of `es` is a fault event. -/
def FaultFree (isFault : Event → Bool) (es : List Event) : Prop :=
  ∀ e ∈ es, isFault e = false

/-- Some event of `es` is a fault event. -/
def HasFault (isFault : Event → Bool) (es : List Event) : Prop :=
  ∃ e ∈ es, isFault e = true

theorem not_faultFree_iff_hasFault (isFault : Event → Bool) (es : List Event) :
    ¬ FaultFree isFault es ↔ HasFault isFault es := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hcon
    apply h
    intro e he
    cases hb : isFault e with
    | false => rfl
    | true => exact absurd ⟨e, he, hb⟩ hcon
  · rintro ⟨e, he, hb⟩ hFF
    exact absurd (hFF e he ▸ hb) (by decide)

theorem faultThenN_hasFault {isFault : Event → Bool} {N : Nat} {es : List Event}
    (h : FaultThenN isFault N es) : HasFault isFault es := by
  obtain ⟨pre, e, suf, heq, hf, _⟩ := h
  exact ⟨e, heq ▸ List.mem_append.mpr (Or.inr (List.mem_cons_self)), hf⟩

/-- A run satisfying `FaultThenN N` has length at least `N + 1` (the fault event itself,
    plus its `N`-long tail). Used to rule out too-short runs by a plain length count,
    without needing to pin down which event is the fault. -/
theorem faultThenN_length {isFault : Event → Bool} {N : Nat} {es : List Event}
    (h : FaultThenN isFault N es) : N + 1 ≤ es.length := by
  obtain ⟨pre, e, suf, heq, _, hlen⟩ := h
  have hL : es.length = pre.length + suf.length + 1 := by
    subst heq
    simp only [List.length_append, List.length_cons]
    omega
  omega

/-! ### `NDiagnosable` -/

/-- Every run containing a fault, extended by at least `N` further events, has an
    observable projection that no fault-free run shares. -/
def NDiagnosable (step : State → Event → State → Prop) (init : State) (observable : Event → Bool)
    (isFault : Event → Bool) (N : Nat) : Prop :=
  ∀ es, Run step init es → FaultThenN isFault N es →
    ∀ es', Run step init es' → FaultFree isFault es' → proj observable es' ≠ proj observable es

/-! ### (b) Monotonicity -/

/-- **`N`-diagnosable implies `M`-diagnosable for every `M ≥ N`.** A smaller required
    post-fault delay is the stronger property. -/
theorem nDiagnosable_mono {step : State → Event → State → Prop} {init : State}
    {observable isFault : Event → Bool} {N M : Nat} (hNM : N ≤ M)
    (h : NDiagnosable step init observable isFault N) :
    NDiagnosable step init observable isFault M := by
  intro es hRun hFTM es' hRun' hFF
  obtain ⟨pre, e, suf, heq, hf, hlen⟩ := hFTM
  have hFTN : FaultThenN isFault N es := ⟨pre, e, suf, heq, hf, Nat.le_trans hNM hlen⟩
  exact h es hRun hFTN es' hRun' hFF

/-! ### (c) The detection payload -/

/-- Under `NDiagnosable N`, a fault-then-`N` run and any run sharing its observable
    projection cannot be fault-free. -/
theorem nDiagnosable_detects {step : State → Event → State → Prop} {init : State}
    {observable isFault : Event → Bool} {N : Nat}
    (h : NDiagnosable step init observable isFault N)
    {es es' : List Event} (hRun : Run step init es) (hFTN : FaultThenN isFault N es)
    (hRun' : Run step init es') (hProjEq : proj observable es' = proj observable es) :
    ¬ FaultFree isFault es' := by
  intro hFF
  exact (h es hRun hFTN es' hRun' hFF) hProjEq

theorem nDiagnosable_detects_hasFault {step : State → Event → State → Prop} {init : State}
    {observable isFault : Event → Bool} {N : Nat}
    (h : NDiagnosable step init observable isFault N)
    {es es' : List Event} (hRun : Run step init es) (hFTN : FaultThenN isFault N es)
    (hRun' : Run step init es') (hProjEq : proj observable es' = proj observable es) :
    HasFault isFault es' :=
  (not_faultFree_iff_hasFault isFault es').mp (nDiagnosable_detects h hRun hFTN hRun' hProjEq)

/-! ### (d) Instances -/

section Instances

/-! #### Positive: a fault always produces a distinguishing observable event -/

inductive Event3 where
  | obsA | obsB | fault
deriving DecidableEq

/-- `obsA`, `obsB` observable; `fault` unobservable. -/
def observable3 : Event3 → Bool
  | .obsA => true
  | .obsB => true
  | .fault => false

def isFault3 : Event3 → Bool
  | .fault => true
  | _ => false

inductive PState where
  | s0 | s1 | s2 | s3
deriving DecidableEq

/-- `s0 --obsA--> s1` (fault-free, dead end); `s0 --fault--> s2 --obsB--> s3` (faulty,
    the fault is immediately followed by the observable `obsB`). -/
inductive posStep : PState → Event3 → PState → Prop where
  | toS1 : posStep .s0 .obsA .s1
  | toS2 : posStep .s0 .fault .s2
  | toS3 : posStep .s2 .obsB .s3

/-- The automaton is small and acyclic: every reachable run from `s0` is one of exactly
    four possibilities. -/
theorem posRun_cases {es : List Event3} {s : PState} (h : Reach posStep .s0 es s) :
    (es = [] ∧ s = .s0) ∨ (es = [.obsA] ∧ s = .s1) ∨ (es = [.fault] ∧ s = .s2) ∨
      (es = [.fault, .obsB] ∧ s = .s3) := by
  cases h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons h1 h2 =>
    cases h1 with
    | toS1 =>
      cases h2 with
      | nil => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | cons h1' _h2' => cases h1'
    | toS2 =>
      cases h2 with
      | nil => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      | cons h1' h2' =>
        cases h1' with
        | toS3 =>
          cases h2' with
          | nil => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
          | cons h1'' _h2'' => cases h1''

/-- **Positive witness.** The system is diagnosable at delay `1`: a fault run's tail is
    always `[obsB]` (observable), which no fault-free reachable run's projection matches
    (`[]` or `[obsA]`). Decided over the fully enumerated finite run set. -/
theorem posDiagnosable : NDiagnosable posStep .s0 observable3 isFault3 1 := by
  intro es hRun hFTN es' hRun' hFF
  obtain ⟨s, hReach⟩ := hRun
  obtain ⟨s', hReach'⟩ := hRun'
  -- The automaton is acyclic: `es` is one of exactly four reachable runs. Only the run
  -- containing the fault (`[fault, obsB]`, length 2) can satisfy `FaultThenN 1`, since
  -- every other reachable run has length < 2 (`faultThenN_length` forces length ≥ 2).
  rcases posRun_cases hReach with ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩
  · exact absurd (faultThenN_length hFTN) (by subst heq; decide)
  · exact absurd (faultThenN_length hFTN) (by subst heq; decide)
  · exact absurd (faultThenN_length hFTN) (by subst heq; decide)
  · subst heq
    -- `es = [fault, obsB]`; case on the (again exactly four) reachable `es'`.
    rcases posRun_cases hReach' with ⟨heq', _⟩ | ⟨heq', _⟩ | ⟨heq', _⟩ | ⟨heq', _⟩ <;> subst heq'
    · decide
    · decide
    · decide
    · exact absurd (hFF Event3.fault (by decide)) (by decide)

/-! #### Negative: a fault followed only by unobservable events is invisible -/

/-- All events unobservable except by name; `fault` marks the fault. -/
def observableN : Event3 → Bool
  | _ => false

/-- `n0 --fault--> n1 --tau...` reusing `Event3.obsA` as a stand-in silent `tau` event
    (its OBSERVABLE status is what matters here, not its name — `observableN` makes it
    unobservable regardless). -/
inductive NState where
  | n0 | n1 | n2 | n3 | m1 | m2 | m3
deriving DecidableEq

/-- Fault branch: `n0 --fault--> n1 --obsA(unobs here)--> n2 --obsA(unobs here)--> n3`.
    Fault-free branch of the SAME length: `n0 --obsA(unobs here)--> m1 --obsA(unobs
    here)--> m2 --obsA(unobs here)--> m3`. Both branches are entirely unobservable under
    `observableN`, so their projections coincide. -/
inductive negStep : NState → Event3 → NState → Prop where
  | faultStep : negStep .n0 .fault .n1
  | tau1 : negStep .n1 .obsA .n2
  | tau2 : negStep .n2 .obsA .n3
  | branch : negStep .n0 .obsA .m1
  | tau3 : negStep .m1 .obsA .m2
  | tau4 : negStep .m2 .obsA .m3

theorem neg_faultRun : Run negStep .n0 [Event3.fault, Event3.obsA, Event3.obsA] :=
  ⟨.n3, Reach.cons negStep.faultStep (Reach.cons negStep.tau1 (Reach.cons negStep.tau2 (Reach.nil _)))⟩

theorem neg_faultFreeRun : Run negStep .n0 [Event3.obsA, Event3.obsA, Event3.obsA] :=
  ⟨.m3, Reach.cons negStep.branch (Reach.cons negStep.tau3 (Reach.cons negStep.tau4 (Reach.nil _)))⟩

theorem neg_faultRun_FaultThenN2 : FaultThenN isFault3 2 [Event3.fault, Event3.obsA, Event3.obsA] :=
  ⟨[], Event3.fault, [Event3.obsA, Event3.obsA], rfl, rfl, by decide⟩

theorem neg_faultFreeRun_isFaultFree : FaultFree isFault3 [Event3.obsA, Event3.obsA, Event3.obsA] := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h | h | h <;> subst h <;> decide

/-- **Negative witness.** The system is NOT diagnosable at delay `2`: the fault run
    `[fault, obsA, obsA]` and the fault-free run `[obsA, obsA, obsA]` share the SAME
    (empty) observable projection under `observableN` — the fault is invisible. -/
theorem neg_not_diagnosable_2 : ¬ NDiagnosable negStep .n0 observableN isFault3 2 := by
  intro h
  exact (h _ neg_faultRun neg_faultRun_FaultThenN2 _ neg_faultFreeRun neg_faultFreeRun_isFaultFree)
    (by decide)

end Instances

end AutoproverCorpus.Diagnosability
