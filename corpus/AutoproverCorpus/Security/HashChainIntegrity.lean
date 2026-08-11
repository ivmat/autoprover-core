/-
  AutoproverCorpus.Security.HashChainIntegrity

  Hash-chain integrity: with the link function taken abstractly injective, equal tips at equal
  length force equal histories. The link function models an idealized injective hash; no
  cryptographic collision-resistance claim is made about any concrete hash — injectivity is an
  explicit hypothesis, not proved.

  Attribution: Classical (Merkle, 1979; transparency-log folklore).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.HashChainIntegrity

variable {D Entry : Type}

def LinkInjective (link : D → Entry → D) : Prop :=
  ∀ d d' e e', link d e = link d' e' → d = d' ∧ e = e'

/-- The tip of the hash chain started at genesis `g`, after appending the entries of
    `l` in order — a LEFT fold: `chain link g (e :: l) = chain link (link g e) l`. -/
def chain (link : D → Entry → D) (g : D) (l : List Entry) : D :=
  l.foldl link g

@[simp] theorem chain_nil (link : D → Entry → D) (g : D) :
    chain link g ([] : List Entry) = g := rfl

@[simp] theorem chain_cons (link : D → Entry → D) (g : D) (e : Entry) (l : List Entry) :
    chain link g (e :: l) = chain link (link g e) l := rfl

/-- The outermost `link` application in a left fold is on the LAST entry: appending one
    entry `e` after a chain `g … l` produces `link (chain link g l) e`. This is the
    fact that makes tail-peeling induction (not head-peeling) the route for (a) — see
    the header's FOLD-DIRECTION NOTE. -/
theorem chain_append_singleton (link : D → Entry → D) (g : D) (l : List Entry) (e : Entry) :
    chain link g (l ++ [e]) = link (chain link g l) e := by
  unfold chain
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

section
variable (link : D → Entry → D)

/-! ### (a) Equal-length equal-tip ⇒ equal history -/

/-- Auxiliary for (a): proved by ordinary (head/cons) induction on `r1`, where `r1` and
    `r2` stand for `l1.reverse`/`l2.reverse` — i.e. this IS the tail-peeling induction
    on `l1`/`l2` from the header's FOLD-DIRECTION NOTE, phrased as a head-induction on
    the reversed lists. -/
private theorem chain_reverse_injective_aux (hInj : LinkInjective link) (g : D) :
    ∀ r1 r2 : List Entry, r1.length = r2.length →
      chain link g r1.reverse = chain link g r2.reverse → r1.reverse = r2.reverse := by
  intro r1
  induction r1 with
  | nil =>
    intro r2 hlen _
    cases r2 with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons e r1' ih =>
    intro r2 hlen heq
    cases r2 with
    | nil => simp at hlen
    | cons e' r2' =>
      simp only [List.length_cons] at hlen
      have hlen' : r1'.length = r2'.length := by omega
      simp only [List.reverse_cons] at heq
      rw [chain_append_singleton, chain_append_singleton] at heq
      obtain ⟨hc, he⟩ := hInj _ _ _ _ heq
      have hrec := ih r2' hlen' hc
      simp only [List.reverse_cons, hrec, he]

/-- **(a) Equal-length equal-tip ⇒ equal history.** With `link` abstractly injective,
    two histories of the same length that reach the same tip from the same genesis are
    the same history. -/
theorem chain_injective_of_length_eq (hInj : LinkInjective link) (g : D)
    (l1 l2 : List Entry) (hlen : l1.length = l2.length)
    (heq : chain link g l1 = chain link g l2) : l1 = l2 := by
  have h := chain_reverse_injective_aux link hInj g l1.reverse l2.reverse
    (by simpa using hlen) (by simpa using heq)
  simpa using h

/-! ### (b) Append/prefix fact -/

/-- **(b) Append/prefix fact.** The tip after appending one entry determines both the
    PRIOR tip and the appended entry — a direct corollary of `LinkInjective` via
    `chain_append_singleton` (which isolates the single outermost `link`
    application at the tip; no length hypothesis is needed). -/
theorem chain_snoc_injective (hInj : LinkInjective link) (g : D)
    (l l' : List Entry) (e e' : Entry)
    (heq : chain link g (l ++ [e]) = chain link g (l' ++ [e'])) :
    chain link g l = chain link g l' ∧ e = e' := by
  rw [chain_append_singleton, chain_append_singleton] at heq
  exact hInj _ _ _ _ heq

/-! ### (c) The injective hash chain determines its history -/

/-- **(c) Global form** — the contrapositive of (a): two histories of
    equal length that differ cannot share a tip (altering the history changes the tip).
    This is a property of an idealized, abstractly injective link function; no
    cryptographic collision-resistance claim is made about any concrete hash. -/
theorem injective_hash_chain_determines_history (hInj : LinkInjective link) (g : D)
    (l1 l2 : List Entry) (hlen : l1.length = l2.length) (hne : l1 ≠ l2) :
    chain link g l1 ≠ chain link g l2 := by
  intro heq
  exact hne (chain_injective_of_length_eq link hInj g l1 l2 hlen heq)

/-- **(c) Positional form** — altering any single entry (at any index
    `i`) of an equal-length history changes the tip: if two equal-length histories
    differ at index `i`, they cannot share a tip. Derives `l1 ≠ l2` from the index
    mismatch and applies `injective_hash_chain_determines_history`. Same idealized-hash
    scoping as the global form above. -/
theorem injective_hash_chain_determines_history_at_position (hInj : LinkInjective link) (g : D)
    (l1 l2 : List Entry) (hlen : l1.length = l2.length)
    (i : Nat) (hdiff : l1[i]? ≠ l2[i]?) :
    chain link g l1 ≠ chain link g l2 := by
  apply injective_hash_chain_determines_history link hInj g l1 l2 hlen
  intro heq
  exact hdiff (by rw [heq])

end

/-! ### (d) Instances: a concrete injective instance -/

def concreteLink (d : Nat) (e : Bool) : Nat :=
  match e with
  | true => 2 * d + 1
  | false => 2 * d

/-- The concrete link is genuinely injective — PROVED, not assumed, by case-splitting
    on the two bits and closing the resulting linear/parity arithmetic with `omega`. -/
theorem concreteLink_injective : LinkInjective concreteLink := by
  intro d d' e e' h
  cases e <;> cases e' <;> simp only [concreteLink] at h
  · exact ⟨by omega, rfl⟩
  · exact absurd h (by omega)
  · exact absurd h (by omega)
  · exact ⟨by omega, rfl⟩

/-- Two different equal-length histories from genesis `0` give different tips — the
    executable, `decide`d witness that (a)/(c) are not vacuous. -/
theorem two_histories_diverge :
    chain concreteLink 0 [true, false] ≠ chain concreteLink 0 [false, true] := by decide

end AutoproverCorpus.HashChainIntegrity
