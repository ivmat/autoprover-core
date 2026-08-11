/-
  AutoproverCorpus.Distributed.TwoPhaseCommitMachine

  Two-phase commit over an explicit state machine - participant states, messages, coordinator
  log, crash and recovery - with the safety invariant that no reachable state has one
  participant committed and another aborted.

  Attribution: Classical (Gray, 1978).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.TwoPhaseCommitMachine

inductive PState where
  | working
  | prepared
  | committed
  | aborted
  deriving DecidableEq, Repr

/-- A participant's vote. -/
inductive Vote where
  | yes
  | no
  deriving DecidableEq, Repr

/-- The coordinator's broadcast decision. -/
inductive Decision where
  | commit
  | abort
  deriving DecidableEq, Repr

/-- The coordinator's own state: still collecting votes, has decided (and logged) `d`,
    or has crashed. -/
inductive CState where
  | collecting
  | decided (d : Decision)
  | crashed
  deriving DecidableEq, Repr

/-- The message set: a vote traveling from participant `p` to the coordinator, or a
    decision traveling from the coordinator to participant `p`. -/
inductive Msg (P : Type) where
  | vote (p : P) (v : Vote)
  | decision (p : P) (d : Decision)
  deriving DecidableEq, Repr

/-- The global system state: per-participant local state, the coordinator's collected
    votes, the coordinator's own state, its persistent log, and the in-flight message
    set. -/
structure GlobalState (P : Type) where
  pstate : P → PState
  votes : P → Option Vote
  cstate : CState
  clog : Option Decision
  inFlight : List (Msg P)

/-- The canonical initial state: every participant `working`, no votes collected, the
    coordinator `collecting` with an empty log, no messages in flight. -/
def initState (P : Type) : GlobalState P :=
  { pstate := fun _ => PState.working
    votes := fun _ => none
    cstate := CState.collecting
    clog := none
    inFlight := [] }

section Model

variable {P : Type} [DecidableEq P] (participants : List P)

inductive Step : GlobalState P → GlobalState P → Prop where
  /-- A `working` participant votes: moves to `prepared` and emits a `vote` message
      (no coordinator involvement yet — this is the participant's own choice). -/
  | partVote {s : GlobalState P} (p : P) (v : Vote) (hw : s.pstate p = PState.working) :
      Step s { s with
        pstate := fun q => if q = p then PState.prepared else s.pstate q
        inFlight := Msg.vote p v :: s.inFlight }
  /-- The coordinator absorbs a DELIVERED vote message into its own record, only while
      still `collecting`. -/
  | coordCollect {s : GlobalState P} (p : P) (v : Vote)
      (hcollecting : s.cstate = CState.collecting) (hmem : Msg.vote p v ∈ s.inFlight) :
      Step s { s with votes := fun q => if q = p then some v else s.votes q }
  /-- **COMMIT** — the ONLY route to a commit decision: every participant's collected
      vote is `yes`. Logs the decision and broadcasts a decision message to every
      participant. -/
  | coordDecideCommit {s : GlobalState P} (hcollecting : s.cstate = CState.collecting)
      (hallYes : ∀ p ∈ participants, s.votes p = some Vote.yes) :
      Step s { s with
        cstate := CState.decided Decision.commit
        clog := some Decision.commit
        inFlight := s.inFlight ++ participants.map (fun p => Msg.decision p Decision.commit) }
  /-- **ABORT** — a witnessed `no` vote is enough to abort. Logs the decision and
      broadcasts a decision message to every participant. -/
  | coordDecideAbort {s : GlobalState P} (hcollecting : s.cstate = CState.collecting)
      (hsomeNo : ∃ p ∈ participants, s.votes p = some Vote.no) :
      Step s { s with
        cstate := CState.decided Decision.abort
        clog := some Decision.abort
        inFlight := s.inFlight ++ participants.map (fun p => Msg.decision p Decision.abort) }
  /-- The coordinator may crash from ANY state, unconditionally. -/
  | coordCrash {s : GlobalState P} : Step s { s with cstate := CState.crashed }
  /-- Recovery, log non-empty: the coordinator re-reads its persistent log and restores
      exactly the logged decision — it does NOT re-decide. -/
  | coordRecoverToLogged {s : GlobalState P} {d : Decision}
      (hcrashed : s.cstate = CState.crashed) (hlog : s.clog = some d) :
      Step s { s with cstate := CState.decided d }
  /-- Recovery, log empty: no decision was ever logged, so the coordinator resumes
      collecting. -/
  | coordRecoverToCollecting {s : GlobalState P} (hcrashed : s.cstate = CState.crashed)
      (hlog : s.clog = none) :
      Step s { s with cstate := CState.collecting }
  /-- A `prepared` participant that has a matching decision message sitting in
      `inFlight` (possibly delivered late, out of order relative to other messages,
      since `inFlight` is an unordered set-as-list) may consume it and decide. A
      message never picked up by this step is, precisely, a dropped/undelivered
      message. -/
  | deliverDecision {s : GlobalState P} (p : P) (d : Decision)
      (hmem : Msg.decision p d ∈ s.inFlight) (hprep : s.pstate p = PState.prepared) :
      Step s { s with
        pstate := fun q =>
          if q = p then (if d = Decision.commit then PState.committed else PState.aborted)
          else s.pstate q }

/-- Reachability: the reflexive-transitive closure of `Step`, rooted at the canonical
    `initState`. -/
inductive Reachable : GlobalState P → Prop where
  | init : Reachable (initState P)
  | step {s s' : GlobalState P} (hr : Reachable s) (hst : Step participants s s') :
      Reachable s'

/-- **The invariant** — see header for the full explanation of each field and why their
    conjunction gives a genuine, non-definitional agreement proof. -/
structure Inv (s : GlobalState P) : Prop where
  collectingImpliesNoLog : s.cstate = CState.collecting → s.clog = none
  logConsistent : ∀ p d, Msg.decision p d ∈ s.inFlight → s.clog = some d
  committedHasMsg : ∀ p, s.pstate p = PState.committed → Msg.decision p Decision.commit ∈ s.inFlight
  abortedHasMsg : ∀ p, s.pstate p = PState.aborted → Msg.decision p Decision.abort ∈ s.inFlight
  logCommitValid : s.clog = some Decision.commit → ∀ p ∈ participants, s.votes p = some Vote.yes

/-- **THE REACHABILITY INDUCTION.** Every reachable state satisfies `Inv`. Proved by
    induction over the `Reachable` derivation, case-split on every `Step` constructor —
    see the header for the per-case argument. -/
theorem invariant_holds {s : GlobalState P} (h : Reachable participants s) :
    Inv participants s := by
  induction h with
  | init =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro _; rfl
    · intro p d hmem; cases hmem
    · intro p hp
      dsimp only [initState] at hp
      exact absurd hp (by decide)
    · intro p hp
      dsimp only [initState] at hp
      exact absurd hp (by decide)
    · intro hclog
      dsimp only [initState] at hclog
      exact absurd hclog (by decide)
  | step _hr hst ih =>
    cases hst with
    | partVote p v hw =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hcol; exact ih.collectingImpliesNoLog hcol
      · intro p' d' hmem'
        rw [List.mem_cons] at hmem'
        rcases hmem' with heq | hmem'
        · simp at heq
        · exact ih.logConsistent p' d' hmem'
      · intro p' hp'
        dsimp only at hp'
        by_cases hcase : p' = p
        · rw [if_pos hcase] at hp'
          exact absurd hp' (by decide)
        · rw [if_neg hcase] at hp'
          exact List.mem_cons_of_mem _ (ih.committedHasMsg p' hp')
      · intro p' hp'
        dsimp only at hp'
        by_cases hcase : p' = p
        · rw [if_pos hcase] at hp'
          exact absurd hp' (by decide)
        · rw [if_neg hcase] at hp'
          exact List.mem_cons_of_mem _ (ih.abortedHasMsg p' hp')
      · intro hclog; exact ih.logCommitValid hclog
    | coordCollect p v hcollecting hmem =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hcol; exact ih.collectingImpliesNoLog hcol
      · intro p' d' hmem'; exact ih.logConsistent p' d' hmem'
      · intro p' hp'; exact ih.committedHasMsg p' hp'
      · intro p' hp'; exact ih.abortedHasMsg p' hp'
      · intro hclog'
        exfalso
        have hnone := ih.collectingImpliesNoLog hcollecting
        rw [hnone] at hclog'
        exact absurd hclog' (by simp)
    | coordDecideCommit hcollecting hallYes =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hcol; exact absurd hcol (by simp)
      · intro p' d' hmem'
        rw [List.mem_append] at hmem'
        rcases hmem' with hold | hnew
        · exfalso
          have hnone := ih.collectingImpliesNoLog hcollecting
          have hsome := ih.logConsistent p' d' hold
          rw [hnone] at hsome
          exact absurd hsome (by simp)
        · obtain ⟨p'', hp'', heq⟩ := List.mem_map.mp hnew
          injection heq with h1 h2
          rw [← h2]
      · intro p' hp'
        exact List.mem_append.mpr (Or.inl (ih.committedHasMsg p' hp'))
      · intro p' hp'
        exact List.mem_append.mpr (Or.inl (ih.abortedHasMsg p' hp'))
      · intro _; exact hallYes
    | coordDecideAbort hcollecting hsomeNo =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hcol; exact absurd hcol (by simp)
      · intro p' d' hmem'
        rw [List.mem_append] at hmem'
        rcases hmem' with hold | hnew
        · exfalso
          have hnone := ih.collectingImpliesNoLog hcollecting
          have hsome := ih.logConsistent p' d' hold
          rw [hnone] at hsome
          exact absurd hsome (by simp)
        · obtain ⟨p'', hp'', heq⟩ := List.mem_map.mp hnew
          injection heq with h1 h2
          rw [← h2]
      · intro p' hp'
        exact List.mem_append.mpr (Or.inl (ih.committedHasMsg p' hp'))
      · intro p' hp'
        exact List.mem_append.mpr (Or.inl (ih.abortedHasMsg p' hp'))
      · intro hclog'; exact absurd hclog' (by simp)
    | coordCrash =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hcol; exact absurd hcol (by simp)
      · intro p' d' hmem'; exact ih.logConsistent p' d' hmem'
      · intro p' hp'; exact ih.committedHasMsg p' hp'
      · intro p' hp'; exact ih.abortedHasMsg p' hp'
      · intro hclog; exact ih.logCommitValid hclog
    | coordRecoverToLogged hcrashed hlog =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hcol; exact absurd hcol (by simp)
      · intro p' d' hmem'; exact ih.logConsistent p' d' hmem'
      · intro p' hp'; exact ih.committedHasMsg p' hp'
      · intro p' hp'; exact ih.abortedHasMsg p' hp'
      · intro hclog; exact ih.logCommitValid hclog
    | coordRecoverToCollecting hcrashed hlog =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro _; exact hlog
      · intro p' d' hmem'; exact ih.logConsistent p' d' hmem'
      · intro p' hp'; exact ih.committedHasMsg p' hp'
      · intro p' hp'; exact ih.abortedHasMsg p' hp'
      · intro hclog; exact ih.logCommitValid hclog
    | deliverDecision p d hmem hprep =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hcol; exact ih.collectingImpliesNoLog hcol
      · intro p' d' hmem'; exact ih.logConsistent p' d' hmem'
      · intro p' hp'
        dsimp only at hp'
        by_cases hcase : p' = p
        · subst hcase
          rw [if_pos rfl] at hp'
          by_cases hd : d = Decision.commit
          · subst hd; exact hmem
          · rw [if_neg hd] at hp'
            exact absurd hp' (by decide)
        · rw [if_neg hcase] at hp'
          exact ih.committedHasMsg p' hp'
      · intro p' hp'
        dsimp only at hp'
        by_cases hcase : p' = p
        · subst hcase
          rw [if_pos rfl] at hp'
          by_cases hd : d = Decision.commit
          · rw [if_pos hd] at hp'
            exact absurd hp' (by decide)
          · have hd' : d = Decision.abort := by
              cases d with
              | commit => exact absurd rfl hd
              | abort => rfl
            subst hd'
            exact hmem
        · rw [if_neg hcase] at hp'
          exact ih.abortedHasMsg p' hp'
      · intro hclog; exact ih.logCommitValid hclog

theorem agreement {s : GlobalState P} (hreach : Reachable participants s) {p q : P}
    (hp : s.pstate p = PState.committed) (hq : s.pstate q = PState.aborted) : False := by
  have hinv := invariant_holds participants hreach
  have hcommitMsg := hinv.committedHasMsg p hp
  have habortMsg := hinv.abortedHasMsg q hq
  have hcommitLog := hinv.logConsistent p Decision.commit hcommitMsg
  have habortLog := hinv.logConsistent q Decision.abort habortMsg
  rw [hcommitLog] at habortLog
  exact absurd habortLog (by decide)

/-- **(a) VALIDITY.** If a reachable state's log records `commit`, every participant's
    collected vote was `yes` — tracked forward through the whole reachability
    induction (`logCommitValid`), so this holds at ANY later reachable point, not only
    at the moment `coordDecideCommit` itself fires. -/
theorem validity {s : GlobalState P} (hreach : Reachable participants s)
    (hclog : s.clog = some Decision.commit) : ∀ p ∈ participants, s.votes p = some Vote.yes :=
  (invariant_holds participants hreach).logCommitValid hclog

/-- **(b) CRASH-SAFETY, general form.** Once a decision is logged at a reachable state,
    NO further step — crash, recovery, a vote, a delivery, or (ruled out via the
    invariant) an attempted fresh decide — ever changes the logged decision. This is
    the structural reason 2PC's coordinator never contradicts itself despite crashing:
    the log, once written, is immutable. -/
theorem no_redecision_after_log {s s' : GlobalState P} {d : Decision}
    (hreach : Reachable participants s) (hlog : s.clog = some d) (hst : Step participants s s') :
    s'.clog = some d := by
  cases hst with
  | partVote _ _ _ => exact hlog
  | coordCollect _ _ _ _ => exact hlog
  | coordDecideCommit hcollecting _ =>
    exfalso
    have hnone := (invariant_holds participants hreach).collectingImpliesNoLog hcollecting
    rw [hnone] at hlog
    exact absurd hlog (by simp)
  | coordDecideAbort hcollecting _ =>
    exfalso
    have hnone := (invariant_holds participants hreach).collectingImpliesNoLog hcollecting
    rw [hnone] at hlog
    exact absurd hlog (by simp)
  | coordCrash => exact hlog
  | coordRecoverToLogged _ _ => exact hlog
  | coordRecoverToCollecting _ hlog' =>
    exfalso
    rw [hlog'] at hlog
    exact absurd hlog (by simp)
  | deliverDecision _ _ _ _ => exact hlog

theorem recovery_restores_logged_decision {s : GlobalState P} {d : Decision}
    (hcrashed : s.cstate = CState.crashed) (hlog : s.clog = some d) :
    Step participants s { s with cstate := CState.decided d } :=
  Step.coordRecoverToLogged hcrashed hlog

end Model

/-! ### (c) Instances: two full, concrete runs over two participants (`Fin 2`) -/

section Instances

abbrev P2 := Fin 2

def participants2 : List P2 := [0, 1]

/-! #### The all-yes run: reaches a state where BOTH participants have `committed`. -/

def cs0 : GlobalState P2 := initState P2

theorem cs0_step1 : Step participants2 cs0 { cs0 with
    pstate := fun q => if q = 0 then PState.prepared else cs0.pstate q
    inFlight := Msg.vote 0 Vote.yes :: cs0.inFlight } :=
  Step.partVote 0 Vote.yes (by decide)

def cs1 : GlobalState P2 := { cs0 with
    pstate := fun q => if q = 0 then PState.prepared else cs0.pstate q
    inFlight := Msg.vote 0 Vote.yes :: cs0.inFlight }

theorem cs1_step2 : Step participants2 cs1 { cs1 with
    pstate := fun q => if q = 1 then PState.prepared else cs1.pstate q
    inFlight := Msg.vote 1 Vote.yes :: cs1.inFlight } :=
  Step.partVote 1 Vote.yes (by decide)

def cs2 : GlobalState P2 := { cs1 with
    pstate := fun q => if q = 1 then PState.prepared else cs1.pstate q
    inFlight := Msg.vote 1 Vote.yes :: cs1.inFlight }

theorem cs2_step3 : Step participants2 cs2 { cs2 with
    votes := fun q => if q = 0 then some Vote.yes else cs2.votes q } :=
  Step.coordCollect 0 Vote.yes (by decide) (by decide)

def cs3 : GlobalState P2 := { cs2 with
    votes := fun q => if q = 0 then some Vote.yes else cs2.votes q }

theorem cs3_step4 : Step participants2 cs3 { cs3 with
    votes := fun q => if q = 1 then some Vote.yes else cs3.votes q } :=
  Step.coordCollect 1 Vote.yes (by decide) (by decide)

def cs4 : GlobalState P2 := { cs3 with
    votes := fun q => if q = 1 then some Vote.yes else cs3.votes q }

theorem cs4_allYes : ∀ p ∈ participants2, cs4.votes p = some Vote.yes := by decide

theorem cs4_step5 : Step participants2 cs4 { cs4 with
    cstate := CState.decided Decision.commit
    clog := some Decision.commit
    inFlight := cs4.inFlight ++ participants2.map (fun p => Msg.decision p Decision.commit) } :=
  Step.coordDecideCommit (by decide) cs4_allYes

def cs5 : GlobalState P2 := { cs4 with
    cstate := CState.decided Decision.commit
    clog := some Decision.commit
    inFlight := cs4.inFlight ++ participants2.map (fun p => Msg.decision p Decision.commit) }

theorem cs5_step6 : Step participants2 cs5 { cs5 with
    pstate := fun q =>
      if q = 0 then (if Decision.commit = Decision.commit then PState.committed else PState.aborted)
      else cs5.pstate q } :=
  Step.deliverDecision 0 Decision.commit (by decide) (by decide)

def cs6 : GlobalState P2 := { cs5 with
    pstate := fun q =>
      if q = 0 then (if Decision.commit = Decision.commit then PState.committed else PState.aborted)
      else cs5.pstate q }

theorem cs6_step7 : Step participants2 cs6 { cs6 with
    pstate := fun q =>
      if q = 1 then (if Decision.commit = Decision.commit then PState.committed else PState.aborted)
      else cs6.pstate q } :=
  Step.deliverDecision 1 Decision.commit (by decide) (by decide)

def cs7 : GlobalState P2 := { cs6 with
    pstate := fun q =>
      if q = 1 then (if Decision.commit = Decision.commit then PState.committed else PState.aborted)
      else cs6.pstate q }

theorem cs7_reachable : Reachable participants2 cs7 :=
  Reachable.step
    (Reachable.step
      (Reachable.step
        (Reachable.step
          (Reachable.step
            (Reachable.step
              (Reachable.step Reachable.init cs0_step1)
              cs1_step2)
            cs2_step3)
          cs3_step4)
        cs4_step5)
      cs5_step6)
    cs6_step7

/-- **(c) Instance, commit run.** Both participants reach `committed`. -/
theorem commit_run_reachable :
    Reachable participants2 cs7 ∧ cs7.pstate 0 = PState.committed ∧
      cs7.pstate 1 = PState.committed :=
  ⟨cs7_reachable, by decide, by decide⟩

/-- `agreement`, exercised concretely on the commit run (with `q := p := 0`/`1`,
    `agreement` would need one `committed` and one `aborted` witness to derive `False`;
    here both are `committed`, so the theorem's HYPOTHESES cannot both be met — this
    sanity check instead confirms `validity` on the concrete run). -/
theorem commit_run_validity : ∀ p ∈ participants2, cs7.votes p = some Vote.yes :=
  validity participants2 cs7_reachable (by decide)

/-! #### The one-no run: reaches a state where BOTH participants have `aborted`. -/

def as0 : GlobalState P2 := initState P2

theorem as0_step1 : Step participants2 as0 { as0 with
    pstate := fun q => if q = 0 then PState.prepared else as0.pstate q
    inFlight := Msg.vote 0 Vote.no :: as0.inFlight } :=
  Step.partVote 0 Vote.no (by decide)

def as1 : GlobalState P2 := { as0 with
    pstate := fun q => if q = 0 then PState.prepared else as0.pstate q
    inFlight := Msg.vote 0 Vote.no :: as0.inFlight }

theorem as1_step2 : Step participants2 as1 { as1 with
    pstate := fun q => if q = 1 then PState.prepared else as1.pstate q
    inFlight := Msg.vote 1 Vote.yes :: as1.inFlight } :=
  Step.partVote 1 Vote.yes (by decide)

def as2 : GlobalState P2 := { as1 with
    pstate := fun q => if q = 1 then PState.prepared else as1.pstate q
    inFlight := Msg.vote 1 Vote.yes :: as1.inFlight }

theorem as2_step3 : Step participants2 as2 { as2 with
    votes := fun q => if q = 0 then some Vote.no else as2.votes q } :=
  Step.coordCollect 0 Vote.no (by decide) (by decide)

def as3 : GlobalState P2 := { as2 with
    votes := fun q => if q = 0 then some Vote.no else as2.votes q }

theorem as3_someNo : ∃ p ∈ participants2, as3.votes p = some Vote.no := by decide

theorem as3_step4 : Step participants2 as3 { as3 with
    cstate := CState.decided Decision.abort
    clog := some Decision.abort
    inFlight := as3.inFlight ++ participants2.map (fun p => Msg.decision p Decision.abort) } :=
  Step.coordDecideAbort (by decide) as3_someNo

def as4 : GlobalState P2 := { as3 with
    cstate := CState.decided Decision.abort
    clog := some Decision.abort
    inFlight := as3.inFlight ++ participants2.map (fun p => Msg.decision p Decision.abort) }

theorem as4_step5 : Step participants2 as4 { as4 with
    pstate := fun q =>
      if q = 0 then (if Decision.abort = Decision.commit then PState.committed else PState.aborted)
      else as4.pstate q } :=
  Step.deliverDecision 0 Decision.abort (by decide) (by decide)

def as5 : GlobalState P2 := { as4 with
    pstate := fun q =>
      if q = 0 then (if Decision.abort = Decision.commit then PState.committed else PState.aborted)
      else as4.pstate q }

theorem as5_step6 : Step participants2 as5 { as5 with
    pstate := fun q =>
      if q = 1 then (if Decision.abort = Decision.commit then PState.committed else PState.aborted)
      else as5.pstate q } :=
  Step.deliverDecision 1 Decision.abort (by decide) (by decide)

def as6 : GlobalState P2 := { as5 with
    pstate := fun q =>
      if q = 1 then (if Decision.abort = Decision.commit then PState.committed else PState.aborted)
      else as5.pstate q }

theorem as6_reachable : Reachable participants2 as6 :=
  Reachable.step
    (Reachable.step
      (Reachable.step
        (Reachable.step
          (Reachable.step
            (Reachable.step Reachable.init as0_step1)
            as1_step2)
          as2_step3)
        as3_step4)
      as4_step5)
    as5_step6

/-- **(c) Instance, abort run.** Both participants reach `aborted`. -/
theorem abort_run_reachable :
    Reachable participants2 as6 ∧ as6.pstate 0 = PState.aborted ∧
      as6.pstate 1 = PState.aborted :=
  ⟨as6_reachable, by decide, by decide⟩

/-- `agreement`, exercised concretely: `cs7` (commit run) has participant `0`
    `committed`; `as6` (abort run) has participant `0` `aborted`. These are two
    DIFFERENT reachable states (different vote histories), so `agreement` does not
    apply across them — that is exactly the point: agreement is a WITHIN-a-single-
    reachable-state guarantee, and no single reachable state here (nor, by the
    theorem, any other) ever has one participant `committed` and another `aborted`
    simultaneously. -/
theorem agreement_holds_within_commit_run :
    ¬ (cs7.pstate 0 = PState.committed ∧ cs7.pstate 1 = PState.aborted) := by
  intro h
  exact agreement participants2 cs7_reachable h.1 h.2

theorem agreement_holds_within_abort_run :
    ¬ (as6.pstate 0 = PState.committed ∧ as6.pstate 1 = PState.aborted) := by
  intro h
  exact agreement participants2 as6_reachable h.1 h.2

end Instances

end AutoproverCorpus.TwoPhaseCommitMachine
