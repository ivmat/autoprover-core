/-
  AutoproverCorpus.Security.OneTimePadPerfectSecrecy

  Shannon's perfect secrecy of the one-time pad, in exact key-counting form. The cipher is
  bitwise XOR of a message with a key of the same length (Vernam's cipher). Three results:

  (1) Correctness (`pad_pad`): decrypting with the same key returns the message.
  (2) **Perfect secrecy** (`perfect_secrecy`): for EVERY message `m` and EVERY ciphertext `c` of
      the same length, there is EXACTLY ONE key of that length encrypting `m` to `c`. Since the
      count is one whatever the message was, an adversary holding only `c` learns nothing about
      `m`: every message of the right length remains possible, and (for a uniformly chosen key)
      equally likely — this is Shannon's condition, stated as an exact-count fact.
  (3) Key reuse breaks it (`key_reuse_leaks`): two messages encrypted under the SAME key satisfy
      `c1 XOR c2 = m1 XOR m2`, so the XOR of the plaintexts leaks in full. The classical caveat
      is proved, not just noted.

  SCOPE. Perfect secrecy is stated in the exact key-count form — "exactly one key per
  (message, ciphertext) pair, for every message" — and the uniform key distribution is an
  assumption discussed here, not a formalized probability measure: no probability space,
  random variable, or conditional distribution appears below. Nothing here is a computational
  or cryptographic-hardness claim; the one-time pad's information-theoretic security is exactly
  the counting fact proved, and it depends on the key being uniform, secret, and used once.

  Attribution: G. S. Vernam, 1926 (the cipher); C. E. Shannon, "Communication Theory of Secrecy
  Systems", Bell System Technical Journal, 1949 (perfect secrecy).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.OneTimePadPerfectSecrecy

/-! ### "Exactly one", spelled out -/

/-- Core Lean has no `∃!` notation, so uniqueness is written out: exactly one `x` satisfies
    `p`. Every perfect-secrecy statement below is an instance of this shape. -/
def ExactlyOne {α : Type} (p : α → Prop) : Prop :=
  ∃ x, p x ∧ ∀ y, p y → y = x

/-! ### The cipher -/

/-- The one-time pad: bitwise XOR of two equal-length bit strings. Encryption and decryption
    are the same operation, which is why no separate decryption function appears below. -/
def pad (m k : List Bool) : List Bool := List.zipWith Bool.xor m k

/-- The ciphertext is as long as the shorter argument; under the equal-length hypothesis used
    throughout, as long as the message. -/
theorem pad_length (m k : List Bool) : (pad m k).length = min m.length k.length := by
  simp [pad]

theorem pad_length_eq {m k : List Bool} (h : m.length = k.length) :
    (pad m k).length = m.length := by
  simp [pad_length, h]

/-! ### Correctness and the cancellation law -/

/-- **Cancellation.** XOR-ing twice with the same left operand is the identity:
    `m XOR (m XOR k) = k`. Proved by induction on `m`, generalizing `k`; the per-bit fact is
    `decide`-checked on the four Boolean cases. Both correctness and uniqueness below are
    corollaries of this one law. -/
theorem pad_left_cancel : ∀ (m k : List Bool), m.length = k.length → pad m (pad m k) = k := by
  intro m
  induction m with
  | nil => intro k hk; cases k with
    | nil => rfl
    | cons b bs => simp at hk
  | cons a as ih =>
    intro k hk
    cases k with
    | nil => simp at hk
    | cons b bs =>
      have hlen : as.length = bs.length := by simpa using hk
      simp only [pad, List.zipWith_cons_cons, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · cases a <;> cases b <;> decide
      · exact ih bs hlen

/-- **Correctness.** Decrypting a ciphertext with the key that produced it returns the message:
    `pad (pad m k) k = m` for equal-length `m` and `k`. -/
theorem pad_pad : ∀ (m k : List Bool), m.length = k.length → pad (pad m k) k = m := by
  intro m
  induction m with
  | nil => intro k hk; cases k with
    | nil => rfl
    | cons b bs => simp at hk
  | cons a as ih =>
    intro k hk
    cases k with
    | nil => simp at hk
    | cons b bs =>
      have hlen : as.length = bs.length := by simpa using hk
      simp only [pad, List.zipWith_cons_cons, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · cases a <;> cases b <;> decide
      · exact ih bs hlen

/-! ### Perfect secrecy: exactly one key per (message, ciphertext) pair -/

/-- **Perfect secrecy (Shannon, 1949), exact-count form.** For every message `m` and every
    ciphertext `c` of the same length, there is exactly one key of that length taking `m` to
    `c` — namely `m XOR c`. Existence and uniqueness are both instances of `pad_left_cancel`.

    The force of the statement is the quantifier order: the count is one for EVERY message, so
    a ciphertext alone excludes no message of the right length. -/
theorem perfect_secrecy (m c : List Bool) (h : m.length = c.length) :
    ExactlyOne (fun k : List Bool => k.length = m.length ∧ pad m k = c) := by
  refine ⟨pad m c, ⟨by simp [pad_length_eq h], pad_left_cancel m c h⟩, ?_⟩
  intro k hk
  have hml : m.length = k.length := hk.1.symm
  calc k = pad m (pad m k) := (pad_left_cancel m k hml).symm
    _ = pad m c := by rw [hk.2]

/-- **The ciphertext excludes no message.** For any two messages of the same length and any
    ciphertext of that length, each message has exactly one key explaining the ciphertext. The
    key count is therefore independent of the message — which, for a uniformly chosen key, is
    precisely "the ciphertext distribution does not depend on the plaintext". -/
theorem key_count_independent_of_message (m1 m2 c : List Bool)
    (h1 : m1.length = c.length) (h2 : m2.length = c.length) :
    ExactlyOne (fun k : List Bool => k.length = m1.length ∧ pad m1 k = c) ∧
    ExactlyOne (fun k : List Bool => k.length = m2.length ∧ pad m2 k = c) :=
  ⟨perfect_secrecy m1 c h1, perfect_secrecy m2 c h2⟩

/-! ### Key reuse destroys the guarantee -/

/-- **Key reuse leaks the XOR of the plaintexts.** If the same key encrypts two messages, then
    `c1 XOR c2 = m1 XOR m2` — the key cancels and the relationship between the plaintexts is
    exposed in full, independently of how the key was chosen. This is the "one-time" in
    one-time pad, proved rather than asserted: `perfect_secrecy` above says nothing about two
    messages sharing a key. -/
theorem key_reuse_leaks : ∀ (m1 m2 k : List Bool), m1.length = k.length → m2.length = k.length →
    pad (pad m1 k) (pad m2 k) = pad m1 m2 := by
  intro m1
  induction m1 with
  | nil => intro m2 k _ _; rfl
  | cons a as ih =>
    intro m2 k h1 h2
    cases k with
    | nil => simp at h1
    | cons c cs =>
      cases m2 with
      | nil => simp at h2
      | cons b bs =>
        have hak : as.length = cs.length := by simpa using h1
        have hbk : bs.length = cs.length := by simpa using h2
        simp only [pad, List.zipWith_cons_cons, List.cons.injEq]
        refine ⟨?_, ?_⟩
        · cases a <;> cases b <;> cases c <;> decide
        · exact ih bs cs hak hbk

/-! ### Instances -/

/-- A concrete 3-bit message and key. -/
abbrev msg : List Bool := [true, false, true]
abbrev key : List Bool := [false, true, true]

/-- The ciphertext, computed. -/
example : pad msg key = [true, true, false] := by decide

/-- Correctness, concretely. -/
example : pad (pad msg key) key = msg := by decide

/-- **Non-vacuity of perfect secrecy.** The unique key carrying `msg` to the ciphertext
    `[false, false, false]` is `[true, false, true]` — a DIFFERENT key from the one above, for
    the same message: every ciphertext is reachable from every message, which is the content of
    the theorem. -/
example : pad msg [true, false, true] = [false, false, false] := by decide

/-- The general theorem applied at this instance. -/
example :
    ExactlyOne (fun k : List Bool => k.length = msg.length ∧ pad msg k = [false, false, false]) :=
  perfect_secrecy msg [false, false, false] (by decide)

/-- **Key reuse, concretely.** Two messages under the same key: the XOR of the ciphertexts
    equals the XOR of the plaintexts, and both are computed here. -/
example :
    pad (pad msg key) (pad [false, false, true] key) = pad msg [false, false, true] := by decide

end AutoproverCorpus.OneTimePadPerfectSecrecy
