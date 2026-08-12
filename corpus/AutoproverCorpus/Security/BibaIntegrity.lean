/-
  AutoproverCorpus.Security.BibaIntegrity

  Biba integrity on a finite integrity lattice: the simple-integrity property (a subject may
  READ an object only if the subject's integrity level does not exceed the object's integrity
  level — "no read down") together with the integrity star-property (a subject may WRITE an
  object only if the object's integrity level does not exceed the subject's integrity level —
  "no write up") together bound the integrity flow of any write-then-read chain through a
  shared object: the reader's integrity level never exceeds the original writer's, so
  information can never flow UP in integrity from a lower-integrity source to a
  higher-integrity subject. A preservation result then shows this combined invariant survives
  any sequence of access grants that are individually safe.

  This is the integrity DUAL of `Security.BellLaPadula`'s confidentiality result: both read and
  write conditions, and the flow theorem, have their inequality direction reversed relative to
  the roles of subject and object. It reuses none of that file's code and is a separate,
  self-contained development.

  Attribution: K. J. Biba, 1977.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.BibaIntegrity

/-- Access modes: read or write. -/
inductive Mode
  | Read
  | Write
  deriving DecidableEq, Repr

/-- A single active access: which subject, which object, in which mode. -/
abbrev Access (Subj Obj : Type) := Subj × Obj × Mode

/-- The state of the system: the set of currently-active accesses, as a list. -/
abbrev State (Subj Obj : Type) := List (Access Subj Obj)

variable {Subj Obj Level : Type} (integrity : Subj → Level) (objIntegrity : Obj → Level)
  (leq : Level → Level → Prop)

/-! ### The two Biba strict-integrity-policy properties -/

/-- **Simple-integrity property ("no read down").** Every active READ access has a reading
    subject whose integrity level flows to (does not exceed) the object's integrity level: a
    subject may not read data of lower integrity than itself. `abbrev` (not `def`), so
    typeclass search can see through it to a `Decidable` instance for `decide` on concrete
    instances — a plain `def` here would leave `decide` unable to unfold it. -/
abbrev SimpleIntegrity (b : State Subj Obj) : Prop :=
  ∀ t ∈ b, t.2.2 = Mode.Read → leq (integrity t.1) (objIntegrity t.2.1)

/-- **Integrity star-property ("no write up").** Every active WRITE access has an object whose
    integrity level flows to (does not exceed) the writing subject's integrity level: a
    subject may not write data of higher integrity than itself. `abbrev`, for the same
    `decide`-transparency reason as `SimpleIntegrity`. -/
abbrev StarIntegrity (b : State Subj Obj) : Prop :=
  ∀ t ∈ b, t.2.2 = Mode.Write → leq (objIntegrity t.2.1) (integrity t.1)

/-- A state is integrity-secure exactly when it satisfies both properties. `abbrev`, for the
    same `decide`-transparency reason. -/
abbrev IntegritySecure (b : State Subj Obj) : Prop :=
  SimpleIntegrity integrity objIntegrity leq b ∧ StarIntegrity integrity objIntegrity leq b

/-! ### (1) The integrity content: no upward information flow through a shared object -/

/-- **No upward flow.** In any integrity-secure state, if subject `sw` writes object `o` and
    subject `sr` reads the SAME object `o`, then `sr`'s integrity level flows to `sw`'s
    integrity level — the dual of `BellLaPadula.no_downward_flow`. Chained directly from
    `SimpleIntegrity` (reader ≤ object) and `StarIntegrity` (object ≤ writer) via `leq`'s
    transitivity: information can never flow from a lower-integrity writer up into a
    higher-integrity reader without violating one of the two properties. -/
theorem no_upward_flow (htrans : ∀ {x y z : Level}, leq x y → leq y z → leq x z)
    {b : State Subj Obj} (hsec : IntegritySecure integrity objIntegrity leq b)
    {sw sr : Subj} {o : Obj} (hw : (sw, o, Mode.Write) ∈ b) (hr : (sr, o, Mode.Read) ∈ b) :
    leq (integrity sr) (integrity sw) :=
  htrans (hsec.1 (sr, o, Mode.Read) hr rfl) (hsec.2 (sw, o, Mode.Write) hw rfl)

/-! ### (2) Preservation under a sequence of individually-safe operations -/

/-- An operation on the state is safe exactly when it maps every integrity-secure state to an
    integrity-secure state. -/
def PreservesIntegrity (op : State Subj Obj → State Subj Obj) : Prop :=
  ∀ b, IntegritySecure integrity objIntegrity leq b →
    IntegritySecure integrity objIntegrity leq (op b)

/-- Running a whole sequence of operations, left to right. -/
def run (ops : List (State Subj Obj → State Subj Obj)) (b0 : State Subj Obj) : State Subj Obj :=
  ops.foldl (fun b op => op b) b0

/-- **Integrity preservation theorem.** If the initial state is integrity-secure and every
    operation in a sequence individually preserves integrity, the state after running the
    whole sequence remains integrity-secure. Proved by induction on the operation list. -/
theorem integrity_preservation_theorem {ops : List (State Subj Obj → State Subj Obj)}
    (hall : ∀ op ∈ ops, PreservesIntegrity integrity objIntegrity leq op)
    {b0 : State Subj Obj} (h0 : IntegritySecure integrity objIntegrity leq b0) :
    IntegritySecure integrity objIntegrity leq (run ops b0) := by
  induction ops generalizing b0 with
  | nil => exact h0
  | cons op rest ih =>
    have hop : PreservesIntegrity integrity objIntegrity leq op := hall op List.mem_cons_self
    have hrest : ∀ op' ∈ rest, PreservesIntegrity integrity objIntegrity leq op' :=
      fun op' hop' => hall op' (List.mem_cons_of_mem op hop')
    exact ih hrest (hop b0 h0)

/-- Grant one new access: prepend it to the current access list. -/
def grantAccess (t : Access Subj Obj) (b : State Subj Obj) : State Subj Obj := t :: b

/-- A single new access is safe to grant exactly when it obeys the property matching its own
    mode. `abbrev`, for the same `decide`-transparency reason as `SimpleIntegrity`. -/
abbrev SafeToGrant (t : Access Subj Obj) : Prop :=
  (t.2.2 = Mode.Read → leq (integrity t.1) (objIntegrity t.2.1)) ∧
  (t.2.2 = Mode.Write → leq (objIntegrity t.2.1) (integrity t.1))

/-- Granting a single safe access preserves integrity. -/
theorem grantAccess_preserves (t : Access Subj Obj)
    (hsafe : SafeToGrant integrity objIntegrity leq t) :
    PreservesIntegrity integrity objIntegrity leq (grantAccess t) := by
  intro b hb
  refine ⟨?_, ?_⟩
  · intro t' ht' hread
    rcases List.mem_cons.mp ht' with rfl | ht'
    · exact hsafe.1 hread
    · exact hb.1 t' ht' hread
  · intro t' ht' hwrite
    rcases List.mem_cons.mp ht' with rfl | ht'
    · exact hsafe.2 hwrite
    · exact hb.2 t' ht' hwrite

/-! ### (3) A concrete finite lattice instance -/

/-- A concrete 3-level integrity lattice: `Low < Medium < High` (`High` = most trusted). -/
inductive ILevel3
  | Low | Medium | High
  deriving DecidableEq, Repr

/-- The lattice order, as a `Bool` test. -/
def ile3B : ILevel3 → ILevel3 → Bool
  | ILevel3.Low, _ => true
  | ILevel3.Medium, ILevel3.Low => false
  | ILevel3.Medium, _ => true
  | ILevel3.High, ILevel3.High => true
  | ILevel3.High, _ => false

abbrev ile3 (a b : ILevel3) : Prop := ile3B a b = true

/-- `ile3` is transitive — checked by cases over all 27 concrete triples of `ILevel3`. -/
theorem ile3_trans : ∀ {x y z : ILevel3}, ile3 x y → ile3 y z → ile3 x z := by
  intro x y z
  cases x <;> cases y <;> cases z <;> decide

/-- Three subjects: `sysAdmin` at `High` integrity, `guest` at `Low`, `auditor` at `High`. -/
inductive ISubj3
  | sysAdmin | guest | auditor
  deriving DecidableEq, Repr

/-- Two objects: a `Low`-integrity scratch file and a `High`-integrity config file. -/
inductive IObj3
  | fileLow | fileHigh
  deriving DecidableEq, Repr

def integrity3 : ISubj3 → ILevel3
  | ISubj3.sysAdmin => ILevel3.High
  | ISubj3.guest => ILevel3.Low
  | ISubj3.auditor => ILevel3.High

def objIntegrity3 : IObj3 → ILevel3
  | IObj3.fileLow => ILevel3.Low
  | IObj3.fileHigh => ILevel3.High

/-- A concrete integrity-secure state: `sysAdmin` (High) writes the High-integrity config
    file, `auditor` (High) reads that same file, and `guest` (Low) reads the Low-integrity
    scratch file. -/
def sampleState : State ISubj3 IObj3 :=
  [(ISubj3.sysAdmin, IObj3.fileHigh, Mode.Write), (ISubj3.auditor, IObj3.fileHigh, Mode.Read),
   (ISubj3.guest, IObj3.fileLow, Mode.Read)]

example : SimpleIntegrity integrity3 objIntegrity3 ile3 sampleState := by decide
example : StarIntegrity integrity3 objIntegrity3 ile3 sampleState := by decide

/-- The concrete instance of `no_upward_flow`: `sysAdmin` writes `fileHigh`, `auditor` reads
    it, and indeed `integrity auditor ≤ integrity sysAdmin` (both `High`) — no upward
    contamination. -/
example : ile3 (integrity3 ISubj3.auditor) (integrity3 ISubj3.sysAdmin) :=
  no_upward_flow integrity3 objIntegrity3 ile3 ile3_trans
    (show IntegritySecure integrity3 objIntegrity3 ile3 sampleState by
      exact ⟨by decide, by decide⟩)
    (show (ISubj3.sysAdmin, IObj3.fileHigh, Mode.Write) ∈ sampleState by decide)
    (show (ISubj3.auditor, IObj3.fileHigh, Mode.Read) ∈ sampleState by decide)

/-- The properties are non-vacuous: `guest` (Low) reading `fileHigh` (High) would be ALLOWED
    by simple-integrity (reading up is fine — it's writing up and reading down that are
    forbidden), but `guest` (Low) WRITING `fileHigh` (High) would VIOLATE the star-integrity
    property — the property genuinely excludes something. -/
example :
    ¬ StarIntegrity integrity3 objIntegrity3 ile3
        [(ISubj3.guest, IObj3.fileHigh, Mode.Write)] := by decide

/-- A concrete `SafeToGrant` instance: granting `guest` a read of `fileHigh` is safe
    (`Low ≤ High`, no read down). -/
example : SafeToGrant integrity3 objIntegrity3 ile3 (ISubj3.guest, IObj3.fileHigh, Mode.Read) := by
  decide

/-- Granting that single safe access from the empty (vacuously integrity-secure) state, via
    `integrity_preservation_theorem`, lands in an integrity-secure state. -/
example :
    IntegritySecure integrity3 objIntegrity3 ile3
      (run [grantAccess (ISubj3.guest, IObj3.fileHigh, Mode.Read)] ([] : State ISubj3 IObj3)) :=
  integrity_preservation_theorem integrity3 objIntegrity3 ile3
    (fun op hop => by
      rw [List.mem_singleton] at hop
      subst hop
      exact grantAccess_preserves integrity3 objIntegrity3 ile3 _ (by decide))
    ⟨by decide, by decide⟩

end AutoproverCorpus.BibaIntegrity
