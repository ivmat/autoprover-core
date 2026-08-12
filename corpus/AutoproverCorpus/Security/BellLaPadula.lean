/-
  AutoproverCorpus.Security.BellLaPadula

  Bell-LaPadula confidentiality on a finite security lattice: the simple-security property (a
  subject may READ an object only if the object's classification does not exceed the
  subject's clearance — "no read up") together with the star-property (a subject may WRITE an
  object only if the subject's clearance does not exceed the object's classification — "no
  write down") together bound the information flow of any write-then-read chain through a
  shared object: the writer's clearance never exceeds the reader's clearance, so information
  can never flow from a higher-cleared subject to a lower-cleared one. A
  Basic-Security-Theorem-style preservation result then shows this combined invariant survives
  any sequence of access grants that are individually safe. This is a state-based
  access-control result, distinct from (and complementary to) the trace-purging unwinding
  results in this corpus's other Security modules.

  Attribution: Bell and LaPadula, 1973.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.BellLaPadula

/-- Access modes: read or write. -/
inductive Mode
  | Read
  | Write
  deriving DecidableEq, Repr

/-- A single active access: which subject, which object, in which mode. -/
abbrev Access (Subj Obj : Type) := Subj × Obj × Mode

/-- The state of the system: the set of currently-active accesses, as a list. -/
abbrev State (Subj Obj : Type) := List (Access Subj Obj)

variable {Subj Obj Level : Type} (clearance : Subj → Level) (classification : Obj → Level)
  (leq : Level → Level → Prop)

/-! ### The two Bell-LaPadula properties -/

/-- **Simple-security property ("no read up").** Every active READ access has an object whose
    classification flows to (does not exceed) the reading subject's clearance. `abbrev` (not
    `def`), so typeclass search can see through it to a `Decidable` instance for `decide` on
    concrete instances — a plain `def` here would leave `decide` unable to unfold it. -/
abbrev SimpleSecurity (b : State Subj Obj) : Prop :=
  ∀ t ∈ b, t.2.2 = Mode.Read → leq (classification t.2.1) (clearance t.1)

/-- **Star-property ("no write down").** Every active WRITE access has a writing subject
    whose clearance flows to (does not exceed) the object's classification. `abbrev`, for the
    same `decide`-transparency reason as `SimpleSecurity`. -/
abbrev StarProperty (b : State Subj Obj) : Prop :=
  ∀ t ∈ b, t.2.2 = Mode.Write → leq (clearance t.1) (classification t.2.1)

/-- A state is secure exactly when it satisfies both properties. `abbrev`, for the same
    `decide`-transparency reason. -/
abbrev Secure (b : State Subj Obj) : Prop :=
  SimpleSecurity clearance classification leq b ∧ StarProperty clearance classification leq b

/-! ### (1) The secrecy content: no downward information flow through a shared object -/

/-- **No downward flow.** In any secure state, if subject `sw` writes object `o` and subject
    `sr` reads the SAME object `o`, then `sw`'s clearance flows to `sr`'s clearance. Chained
    directly from `StarProperty` (writer ≤ object) and `SimpleSecurity` (object ≤ reader) via
    `leq`'s transitivity: information can never flow from a higher-cleared writer to a
    lower-cleared reader without violating one of the two properties. -/
theorem no_downward_flow (htrans : ∀ {x y z : Level}, leq x y → leq y z → leq x z)
    {b : State Subj Obj} (hsec : Secure clearance classification leq b)
    {sw sr : Subj} {o : Obj} (hw : (sw, o, Mode.Write) ∈ b) (hr : (sr, o, Mode.Read) ∈ b) :
    leq (clearance sw) (clearance sr) :=
  htrans (hsec.2 (sw, o, Mode.Write) hw rfl) (hsec.1 (sr, o, Mode.Read) hr rfl)

/-! ### (2) Basic-Security-Theorem-style preservation -/

/-- An operation on the state is safe exactly when it maps every secure state to a secure
    state. -/
def PreservesSecurity (op : State Subj Obj → State Subj Obj) : Prop :=
  ∀ b, Secure clearance classification leq b → Secure clearance classification leq (op b)

/-- Running a whole sequence of operations, left to right. -/
def run (ops : List (State Subj Obj → State Subj Obj)) (b0 : State Subj Obj) : State Subj Obj :=
  ops.foldl (fun b op => op b) b0

/-- **Basic Security Theorem (preservation form).** If the initial state is secure and every
    operation in a sequence individually preserves security, the state after running the whole
    sequence remains secure. Proved by induction on the operation list. -/
theorem basic_security_theorem {ops : List (State Subj Obj → State Subj Obj)}
    (hall : ∀ op ∈ ops, PreservesSecurity clearance classification leq op)
    {b0 : State Subj Obj} (h0 : Secure clearance classification leq b0) :
    Secure clearance classification leq (run ops b0) := by
  induction ops generalizing b0 with
  | nil => exact h0
  | cons op rest ih =>
    have hop : PreservesSecurity clearance classification leq op := hall op List.mem_cons_self
    have hrest : ∀ op' ∈ rest, PreservesSecurity clearance classification leq op' :=
      fun op' hop' => hall op' (List.mem_cons_of_mem op hop')
    exact ih hrest (hop b0 h0)

/-- Grant one new access: prepend it to the current access list. -/
def grantAccess (t : Access Subj Obj) (b : State Subj Obj) : State Subj Obj := t :: b

/-- A single new access is safe to grant exactly when it obeys the property matching its own
    mode. `abbrev`, for the same `decide`-transparency reason as `SimpleSecurity`. -/
abbrev SafeToGrant (t : Access Subj Obj) : Prop :=
  (t.2.2 = Mode.Read → leq (classification t.2.1) (clearance t.1)) ∧
  (t.2.2 = Mode.Write → leq (clearance t.1) (classification t.2.1))

/-- Granting a single safe access preserves security. -/
theorem grantAccess_preserves (t : Access Subj Obj)
    (hsafe : SafeToGrant clearance classification leq t) :
    PreservesSecurity clearance classification leq (grantAccess t) := by
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

/-- A concrete 3-level lattice: `Low < Medium < High`. -/
inductive Level3
  | Low | Medium | High
  deriving DecidableEq, Repr

/-- The lattice order, as a `Bool` test. -/
def le3B : Level3 → Level3 → Bool
  | Level3.Low, _ => true
  | Level3.Medium, Level3.Low => false
  | Level3.Medium, _ => true
  | Level3.High, Level3.High => true
  | Level3.High, _ => false

abbrev le3 (a b : Level3) : Prop := le3B a b = true

/-- `le3` is transitive — checked by cases over all 27 concrete triples of `Level3`. -/
theorem le3_trans : ∀ {x y z : Level3}, le3 x y → le3 y z → le3 x z := by
  intro x y z
  cases x <;> cases y <;> cases z <;> decide

/-- Three subjects: `alice`/`carol` cleared to `High`, `bob` cleared to `Low`. -/
inductive Subj3
  | alice | bob | carol
  deriving DecidableEq, Repr

/-- Two objects: a `Low`-classified file and a `High`-classified file. -/
inductive Obj3
  | fileLow | fileHigh
  deriving DecidableEq, Repr

def clearance3 : Subj3 → Level3
  | Subj3.alice => Level3.High
  | Subj3.bob => Level3.Low
  | Subj3.carol => Level3.High

def classification3 : Obj3 → Level3
  | Obj3.fileLow => Level3.Low
  | Obj3.fileHigh => Level3.High

/-- A concrete secure state: `alice` (High) writes the High file, `carol` (High) reads the
    High file, and `bob` (Low) reads the Low file. -/
def sampleState : State Subj3 Obj3 :=
  [(Subj3.alice, Obj3.fileHigh, Mode.Write), (Subj3.carol, Obj3.fileHigh, Mode.Read),
   (Subj3.bob, Obj3.fileLow, Mode.Read)]

example : SimpleSecurity clearance3 classification3 le3 sampleState := by decide
example : StarProperty clearance3 classification3 le3 sampleState := by decide

/-- The concrete instance of `no_downward_flow`: `alice` writes `fileHigh`, `carol` reads it,
    and indeed `clearance alice ≤ clearance carol` (both `High`) — no downward leak. -/
example : le3 (clearance3 Subj3.alice) (clearance3 Subj3.carol) :=
  no_downward_flow clearance3 classification3 le3 le3_trans
    (show Secure clearance3 classification3 le3 sampleState by
      exact ⟨by decide, by decide⟩)
    (show (Subj3.alice, Obj3.fileHigh, Mode.Write) ∈ sampleState by decide)
    (show (Subj3.carol, Obj3.fileHigh, Mode.Read) ∈ sampleState by decide)

/-- The properties are non-vacuous: `bob` (Low) reading `fileHigh` (High) would VIOLATE
    simple security — the property genuinely excludes something. -/
example :
    ¬ SimpleSecurity clearance3 classification3 le3
        [(Subj3.bob, Obj3.fileHigh, Mode.Read)] := by decide

/-- A concrete `SafeToGrant` instance: granting `bob` a read of `fileLow` is safe
    (`Low ≤ Low`). -/
example : SafeToGrant clearance3 classification3 le3 (Subj3.bob, Obj3.fileLow, Mode.Read) := by
  decide

/-- Granting that single safe access from the empty (vacuously secure) state, via
    `basic_security_theorem`, lands in a secure state. -/
example :
    Secure clearance3 classification3 le3
      (run [grantAccess (Subj3.bob, Obj3.fileLow, Mode.Read)] ([] : State Subj3 Obj3)) :=
  basic_security_theorem clearance3 classification3 le3
    (fun op hop => by
      rw [List.mem_singleton] at hop
      subst hop
      exact grantAccess_preserves clearance3 classification3 le3 _ (by decide))
    ⟨by decide, by decide⟩

end AutoproverCorpus.BellLaPadula
