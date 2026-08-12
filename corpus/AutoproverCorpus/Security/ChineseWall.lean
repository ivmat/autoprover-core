/-
  AutoproverCorpus.Security.ChineseWall

  The Brewer-Nash Chinese Wall policy, simple-security rule: objects are grouped into
  datasets (e.g. "Bank A's files"), and datasets are grouped into conflict-of-interest
  classes (e.g. "Banking"). A subject may access an object only if it has not already
  accessed an object in a DIFFERENT dataset within the SAME conflict-of-interest class — once
  a subject touches one company's data in a conflict class, the "wall" goes up around every
  OTHER company in that same class, for that subject alone (other subjects are unaffected;
  different conflict classes are unaffected). This module models an access history as a
  finite structure, proves the resulting invariant (no two accesses by the same subject to
  different datasets within one conflict class) holds for any history built by a sequence of
  policy-conforming grants, and exhibits a concrete instance with a genuinely BLOCKED
  conflicting access.

  Scope note: this covers the simple-security (read/access) rule only — the classical
  Brewer-Nash paper also has a write extension (a subject may write only if every object it
  has read lies in the same dataset, or a dataset with no conflict-of-interest exposure),
  which this module does not separately formalize.

  Attribution: Brewer and Nash, 1989.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.ChineseWall

/-- One granted access: which subject accessed which object. -/
abbrev Access (Subj Obj : Type) := Subj × Obj

/-- The access history: every access granted so far, in the order granted (most recent
    first). -/
abbrev History (Subj Obj : Type) := List (Access Subj Obj)

variable {Subj Obj Dataset COI : Type} (dataset : Obj → Dataset) (coi : Dataset → COI)

/-! ### The simple-security rule -/

/-- **Simple-security rule for granting a NEW access.** Granting subject `s` access to
    object `o`, given the CURRENT history `hist`, is conforming exactly when: for every prior
    access `(s, o')` by the SAME subject `s` that lies in the SAME conflict-of-interest class
    as `o`, that prior access was to the SAME dataset as `o`. Equivalently, the only thing
    that blocks a request is a prior access by the same subject to a DIFFERENT dataset in the
    SAME conflict class — the classical Chinese Wall "already-in" test. `abbrev` (not `def`),
    so `decide` can unfold it on concrete instances. -/
abbrev ConformingAccess (hist : History Subj Obj) (s : Subj) (o : Obj) : Prop :=
  ∀ p ∈ hist, p.1 = s → coi (dataset p.2) = coi (dataset o) → dataset p.2 = dataset o

/-- **The Chinese Wall invariant.** No two accesses recorded in the history are by the same
    subject, to different datasets, within the same conflict-of-interest class. `abbrev`, for
    the same `decide`-transparency reason as `ConformingAccess`. -/
abbrev NoConflictOfInterest (hist : History Subj Obj) : Prop :=
  ∀ p1 ∈ hist, ∀ p2 ∈ hist, p1.1 = p2.1 → coi (dataset p1.2) = coi (dataset p2.2) →
    dataset p1.2 = dataset p2.2

/-- Grant one new access: prepend it to the current history. -/
def grant (s : Subj) (o : Obj) (hist : History Subj Obj) : History Subj Obj := (s, o) :: hist

/-! ### Preservation under a single conforming grant -/

/-- **Preservation.** Granting a single conforming access to a history that already satisfies
    the invariant keeps the invariant. -/
theorem grant_preserves {hist : History Subj Obj}
    (hinv : NoConflictOfInterest dataset coi hist)
    {s : Subj} {o : Obj} (hconf : ConformingAccess dataset coi hist s o) :
    NoConflictOfInterest dataset coi (grant s o hist) := by
  intro p1 hp1 p2 hp2 hsame hcoi
  rcases List.mem_cons.mp hp1 with rfl | hp1
  · rcases List.mem_cons.mp hp2 with rfl | hp2
    · rfl
    · exact (hconf p2 hp2 hsame.symm hcoi.symm).symm
  · rcases List.mem_cons.mp hp2 with rfl | hp2
    · exact hconf p1 hp1 hsame hcoi
    · exact hinv p1 hp1 p2 hp2 hsame hcoi

/-! ### A policy-conforming history, and the headline theorem -/

/-- **A policy-conforming access history**: built from the empty history by a sequence of
    grants, each of which satisfied `ConformingAccess` against the history accumulated
    strictly before it. Mirrors the `Reachable`-by-transitions style used elsewhere in this
    corpus (e.g. `Concurrency.PetersonMutex`), specialized to the Chinese Wall grant step. -/
inductive ConformingHistory : History Subj Obj → Prop
  | nil : ConformingHistory []
  | step {hist : History Subj Obj} (hprev : ConformingHistory hist)
      {s : Subj} {o : Obj} (hconf : ConformingAccess dataset coi hist s o) :
      ConformingHistory (grant s o hist)

/-- **The Chinese Wall theorem.** Every policy-conforming access history satisfies the
    Chinese Wall invariant: it never contains two accesses by the same subject to different
    datasets within one conflict-of-interest class. Proved by induction on
    `ConformingHistory` — the base case (`[]`) is vacuous, the step case is
    `grant_preserves`. -/
theorem no_conflict_of_interest {hist : History Subj Obj}
    (h : ConformingHistory dataset coi hist) : NoConflictOfInterest dataset coi hist := by
  induction h with
  | nil => intro p1 hp1 _ _ _ _; simp at hp1
  | step _ hconf ih => exact grant_preserves dataset coi ih hconf

/-! ### A concrete finite instance, with a genuinely BLOCKED conflicting access -/

/-- Two conflict-of-interest classes: `Banking` and `Oil`. -/
inductive COI3
  | Banking | Oil
  deriving DecidableEq, Repr

/-- Three datasets: two banks (both `Banking`) and one oil company (`Oil`). -/
inductive Dataset3
  | bankA | bankB | oilA
  deriving DecidableEq, Repr

/-- One object per dataset. -/
inductive Obj3
  | fileBankA | fileBankB | fileOilA
  deriving DecidableEq, Repr

/-- Two subjects. -/
inductive Subj3
  | alice | bob
  deriving DecidableEq, Repr

def dataset3 : Obj3 → Dataset3
  | .fileBankA => .bankA
  | .fileBankB => .bankB
  | .fileOilA => .oilA

def coi3 : Dataset3 → COI3
  | .bankA => .Banking
  | .bankB => .Banking
  | .oilA => .Oil

/-- `alice` has already accessed Bank A's file. -/
def histAliceBankA : History Subj3 Obj3 := grant Subj3.alice Obj3.fileBankA []

/-- **The blocked access.** With `histAliceBankA` on record, `alice` requesting Bank B's file
    is NOT conforming: same subject, same conflict class (`Banking`), different dataset
    (`bankA ≠ bankB`) — exactly the case the rule exists to refuse. This is the non-vacuity
    witness: the rule genuinely excludes a real request. -/
example : ¬ ConformingAccess dataset3 coi3 histAliceBankA Subj3.alice Obj3.fileBankB := by
  decide

/-- The same request from `bob` (a different subject) IS conforming — the wall is
    per-subject, not global. -/
example : ConformingAccess dataset3 coi3 histAliceBankA Subj3.bob Obj3.fileBankB := by decide

/-- `alice` requesting the Oil file IS conforming — different conflict class entirely. -/
example : ConformingAccess dataset3 coi3 histAliceBankA Subj3.alice Obj3.fileOilA := by decide

/-- **The blocked access, as a genuine invariant violation.** If the policy did not block
    `alice`'s conflicting request and it were granted anyway, the resulting history would
    violate the Chinese Wall invariant — showing the rule is doing real preventive work, not
    vacuously always satisfied. -/
example :
    ¬ NoConflictOfInterest dataset3 coi3 (grant Subj3.alice Obj3.fileBankB histAliceBankA) := by
  decide

/-- A genuinely built policy-conforming history: `alice` accesses Bank A, then Oil (both
    conforming), then `bob` accesses Bank B (conforming, different subject) — three real
    grants, none of them the blocked one above. -/
def histFull : History Subj3 Obj3 :=
  grant Subj3.bob Obj3.fileBankB
    (grant Subj3.alice Obj3.fileOilA histAliceBankA)

theorem histFull_conforming : ConformingHistory dataset3 coi3 histFull := by
  apply ConformingHistory.step
  · apply ConformingHistory.step
    · apply ConformingHistory.step
      · exact ConformingHistory.nil
      · decide
    · decide
  · decide

/-- The headline theorem, applied to the concrete built history: `histFull` genuinely
    satisfies the Chinese Wall invariant. -/
theorem histFull_no_conflict : NoConflictOfInterest dataset3 coi3 histFull :=
  no_conflict_of_interest dataset3 coi3 histFull_conforming

end AutoproverCorpus.ChineseWall
