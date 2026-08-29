/-
  AutoproverCorpus.Distributed.TwoGeneralsBoundedImpossibility

  Two Generals impossibility, bounded form: no CONTENT-BLIND, delivery-bit-only (ack-only)
  k-round protocol over a lossy channel can jointly guarantee agreement, attack on a fully
  delivered run, and retreat on total silence - all three clauses are required by the proof
  (agreement plus attack-on-full alone are satisfiable by the constant protocol). Proved general
  in k by a locality/indistinguishability induction.

  Attribution: Classical (Akkoyunlu, Ekanadham and Huber, 1969; Gray, 1978).

  SCOPE NOTE (the schedule is fixed; the protocol class is restricted; the WLOG step is not
  formalized). `Protocol k` below fixes the CANONICAL alternating message schedule: round `i`
  is sent A -> B when `i` is even and B -> A when `i` is odd. The `localA`/`localB` fields go
  further than "decides from the transcript of messages actually delivered": they require each
  party's decision to be a function of the per-round DELIVERY BITS addressed to it, invariant
  under any change to the messages' CONTENT. A deterministic protocol whose decision reads the
  content of a delivered message (e.g. an earlier delivery bit encoded into a later message) can
  violate `localA`/`localB` and so falls outside this `Protocol` type. The impossibility proved
  here is therefore for the strictly smaller class of content-blind, delivery-bit-only (ack-only)
  protocols over that schedule, not for every deterministic protocol over it. The textbook
  argument additionally claims WLOG that an arbitrary `k`-message schedule reduces to the
  alternating one; that reduction is NOT formalized here either, so this module must not be
  cited as the impossibility over an arbitrary message schedule or an arbitrary deterministic
  protocol.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.TwoGeneralsBoundedImpossibility

/-- The adversary: for a `k`-round canonical schedule, `adv i = true` means message `i`
    (0-indexed) is delivered. -/
abbrev Adv (k : Nat) := Fin k → Bool

/-- The all-messages-delivered run (perfect channel). -/
def allTrue (k : Nat) : Adv k := fun _ => true

/-- The all-messages-lost run (total silence). -/
def allFalse (k : Nat) : Adv k := fun _ => false

/-- A `k`-round two-generals protocol over the CANONICAL alternating schedule (round `i`
    sent A→B if `i` even, B→A if `i` odd — see header), restricted to the content-blind,
    delivery-bit-only (ack-only) class: each decision function depends ONLY on the per-round
    DELIVERY BITS of the messages ADDRESSED TO that party, not on their content (`localA`/
    `localB` — a strictly smaller class than all deterministic protocols over the schedule;
    see header). -/
structure Protocol (k : Nat) where
  dA : Adv k → Bool
  dB : Adv k → Bool
  /-- A's decision may depend only on ODD-indexed deliveries (messages B sent to A). -/
  localA : ∀ adv adv' : Adv k,
      (∀ i : Fin k, i.val % 2 = 1 → adv i = adv' i) → dA adv = dA adv'
  /-- B's decision may depend only on EVEN-indexed deliveries (messages A sent to B). -/
  localB : ∀ adv adv' : Adv k,
      (∀ i : Fin k, i.val % 2 = 0 → adv i = adv' i) → dB adv = dB adv'

/-- **AGREEMENT**: the two generals always decide the same, on every adversary schedule. -/
def Agreement {k : Nat} (P : Protocol k) : Prop := ∀ adv : Adv k, P.dA adv = P.dB adv

def AttacksOnFull {k : Nat} (P : Protocol k) : Prop :=
  P.dA (allTrue k) = true ∧ P.dB (allTrue k) = true

def RetreatsOnEmpty {k : Nat} (P : Protocol k) : Prop :=
  P.dA (allFalse k) = false ∧ P.dB (allFalse k) = false

/-! ### (1) REFUTATION of the literal (a) + (b) statement -/

/-- The constant "always attack, ignore every message" protocol. Locality holds
    trivially (the output does not depend on the input at all). -/
def constAttack (k : Nat) : Protocol k where
  dA := fun _ => true
  dB := fun _ => true
  localA := fun _ _ _ => rfl
  localB := fun _ _ _ => rfl

/-- `constAttack` satisfies AGREEMENT — trivially, both decisions are the same literal
    constant on every schedule. -/
theorem constAttack_agreement (k : Nat) : Agreement (constAttack k) := fun _ => rfl

theorem constAttack_attacksOnFull (k : Nat) : AttacksOnFull (constAttack k) := ⟨rfl, rfl⟩

/-- **THE REFUTATION.** `constAttack` does NOT satisfy the repaired clause: it attacks
    even on total silence. This is exactly what the literal (a)+(b) statement fails to
    rule out, and exactly what `RetreatsOnEmpty` restores. -/
theorem constAttack_not_retreatsOnEmpty (k : Nat) : ¬ RetreatsOnEmpty (constAttack k) := by
  intro h
  have hfalse : (true : Bool) = false := h.1
  exact absurd hfalse (by decide)

/-- `dropAdv k j` = the schedule where all messages EXCEPT the last `j` are delivered:
    message `i` (0-indexed) is delivered iff `i + j < k`. `dropAdv k 0 = allTrue k`
    (nothing dropped); `dropAdv k k = allFalse k` (everything dropped); `dropAdv k (j+1)`
    differs from `dropAdv k j` at exactly one index — the classical "suppress the next
    message counting from the end." -/
def dropAdv (k j : Nat) : Adv k := fun i => if i.val + j < k then true else false

theorem dropAdv_zero (k : Nat) : dropAdv k 0 = allTrue k := by
  funext i
  have hik : i.val < k := i.isLt
  unfold dropAdv allTrue
  split
  · rfl
  · exfalso; omega

theorem dropAdv_k (k : Nat) : dropAdv k k = allFalse k := by
  funext i
  unfold dropAdv allFalse
  split
  · exfalso; omega
  · rfl

/-- `dropAdv k (j+1)` and `dropAdv k j` agree at every index EXCEPT possibly the flip
    index `k - 1 - j` — this is the "message absence is indistinguishable" fact, stated
    for an arbitrary index that isn't the one being flipped. -/
theorem dropAdv_succ_agree_off (k j : Nat) {i : Fin k} (hi : i.val ≠ k - 1 - j) :
    dropAdv k (j + 1) i = dropAdv k j i := by
  unfold dropAdv
  split <;> split <;> first | rfl | (exfalso; omega)

theorem attack_persists {k : Nat} (P : Protocol k) (hAgree : Agreement P)
    (hFull : AttacksOnFull P) :
    ∀ j, j ≤ k → P.dA (dropAdv k j) = true ∧ P.dB (dropAdv k j) = true := by
  intro j
  induction j with
  | zero =>
      intro _
      rw [dropAdv_zero k]
      exact hFull
  | succ n ih =>
      intro hn
      obtain ⟨ihA, ihB⟩ := ih (by omega)
      have hcase : (k - 1 - n) % 2 = 0 ∨ (k - 1 - n) % 2 = 1 := by omega
      rcases hcase with hpar | hpar
      · -- the flipped index (k-1-n) is EVEN: addressed to B; A's view is unaffected.
        have hdA : P.dA (dropAdv k (n + 1)) = P.dA (dropAdv k n) := by
          apply P.localA
          intro i hiodd
          exact dropAdv_succ_agree_off k n (by omega)
        have hAt : P.dA (dropAdv k (n + 1)) = true := hdA.trans ihA
        exact ⟨hAt, (hAgree (dropAdv k (n + 1))).symm.trans hAt⟩
      · -- the flipped index (k-1-n) is ODD: addressed to A; B's view is unaffected.
        have hdB : P.dB (dropAdv k (n + 1)) = P.dB (dropAdv k n) := by
          apply P.localB
          intro i hieven
          exact dropAdv_succ_agree_off k n (by omega)
        have hBt : P.dB (dropAdv k (n + 1)) = true := hdB.trans ihB
        exact ⟨(hAgree (dropAdv k (n + 1))).trans hBt, hBt⟩

theorem no_agreement_with_full_attack_and_empty_retreat (k : Nat) :
    ¬ ∃ P : Protocol k, Agreement P ∧ AttacksOnFull P ∧ RetreatsOnEmpty P := by
  rintro ⟨P, hAgree, hFull, hEmpty⟩
  have hall := attack_persists P hAgree hFull k (by omega)
  rw [dropAdv_k k] at hall
  exact absurd (hall.1.symm.trans hEmpty.1) (by decide)

theorem lossyChannel_disagreement_witness {k : Nat} (P : Protocol k)
    (hFull : AttacksOnFull P) (hEmpty : RetreatsOnEmpty P) :
    ∃ adv : Adv k, P.dA adv ≠ P.dB adv := by
  apply Classical.byContradiction
  intro hcon
  apply no_agreement_with_full_attack_and_empty_retreat k
  refine ⟨P, ?_, hFull, hEmpty⟩
  intro adv
  apply Classical.byContradiction
  intro hne
  exact hcon ⟨adv, hne⟩

/-! ### (4) A concrete protocol and a concrete counterexample separating the hypotheses -/

/-- A responsive `k = 2` protocol: "attack iff I received the one message
    addressed to me." Round 0 (even) is A→B, round 1 (odd) is B→A. -/
def echoProtocol : Protocol 2 where
  dA := fun adv => adv 1
  dB := fun adv => adv 0
  localA := fun _ _ h => h 1 (by decide)
  localB := fun _ _ h => h 0 (by decide)

theorem echo_attacksOnFull : AttacksOnFull echoProtocol := ⟨by decide, by decide⟩

theorem echo_retreatsOnEmpty : RetreatsOnEmpty echoProtocol := ⟨by decide, by decide⟩

/-- The adversary that delivers A's order (round 0) but loses B's acknowledgment
    (round 1) — the textbook Two-Generals failure schedule. -/
def separatingAdv : Adv 2 := fun i => decide (i.val = 0)

/-- Counterexample separating the hypotheses: under `separatingAdv`, A never
    hears back and retreats, while B did
    receive the order and attacks — `echoProtocol` meets both non-triviality faces
    (above) yet disagrees here, exactly as `no_agreement_with_full_attack_and_empty_retreat` forces. -/
theorem echo_separating_witness :
    echoProtocol.dA separatingAdv ≠ echoProtocol.dB separatingAdv := by decide

/-- Packaged as the existence form, instantiated concretely (not merely abstractly
    guaranteed by `lossyChannel_disagreement_witness`). -/
theorem echo_disagrees : ∃ adv : Adv 2, echoProtocol.dA adv ≠ echoProtocol.dB adv :=
  ⟨separatingAdv, echo_separating_witness⟩

end AutoproverCorpus.TwoGeneralsBoundedImpossibility
