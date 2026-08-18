/-
  AutoproverCorpus.Security.ShamirThresholdGF5

  Shamir's threshold secret sharing at threshold `t = 2`, over the prime field GF(5), verified
  exhaustively. The dealer picks a secret `a0` and a uniformly random coefficient `a1`, and hands
  participant `x` the share `a0 + a1 * x` (all arithmetic in GF(5) = `Fin 5`); the secret is the
  polynomial's value at `x = 0`, which is never handed out. Two results, the two halves of the
  threshold property:

  (1) **Reconstruction** (`two_shares_determine`): any TWO shares at distinct evaluation points
      determine the whole polynomial — hence the secret. Stated as uniqueness (two polynomials
      agreeing at two distinct points are equal), which is the exact content of the classical
      Lagrange-interpolation argument for `t = 2`, without committing to a formula.

  (2) **Privacy** (`one_share_reveals_nothing`): a participant holding ONE share learns nothing.
      For every evaluation point `x ≠ 0` and every observed value `y`, EVERY candidate secret
      `s` is consistent with exactly one coefficient `a1`. The count is 1 whatever `s` is, so a
      single share excludes no secret, and (for a uniformly chosen `a1`) leaves all five equally
      likely.

  SCOPE (deliberately restricted, and the name says so). This is the fixed instance `t = 2` over
  the fixed field GF(5) — at most four participants, at `x = 1, 2, 3, 4` — checked by exhaustive
  finite enumeration (`decide`), not the general `(t, n)` theorem over an arbitrary finite field.
  Privacy is stated in the exact-count form; no probability measure is formalized, and the
  uniform choice of `a1` is an assumption of the reading, not of the proof. Nothing here is a
  computational or cryptographic-hardness claim.

  Attribution: A. Shamir, "How to Share a Secret", Communications of the ACM, 1979 (G. R.
  Blakley gave an independent threshold scheme, by a different construction, the same year).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.ShamirThresholdGF5

/-! ### The scheme -/

/-- The share handed to participant `x`: the degree-1 polynomial `a0 + a1 * x` evaluated in
    GF(5) (`Fin 5`, whose `+` and `*` are the field operations mod 5). `a0` is the secret, `a1`
    the dealer's random coefficient. `abbrev` so that `decide` can unfold it. -/
abbrev share (a0 a1 x : Fin 5) : Fin 5 := a0 + a1 * x

/-- **The secret is the value at zero.** Participants are given points `x ≠ 0` precisely because
    the share at `x = 0` would be the secret itself. -/
theorem share_at_zero : ∀ a0 a1 : Fin 5, share a0 a1 0 = a0 := by decide

/-! ### (1) Reconstruction: two shares determine the polynomial -/

/-- **Any two shares at distinct points determine the secret.** If two polynomials of this
    family agree at two distinct evaluation points, they have the same secret AND the same
    coefficient — so two participants pooling their shares recover a unique candidate, and it is
    the dealer's. Checked exhaustively over all `5^6 = 15625` combinations of
    `(a0, a1, b0, b1, x, y)`.

    Note what this states and does not state: it is the uniqueness half of Lagrange
    interpolation at `t = 2` (no two distinct polynomials fit both points), not an interpolation
    formula and not a general-degree result. -/
theorem two_shares_determine :
    ∀ a0 a1 b0 b1 x y : Fin 5, x ≠ y →
      share a0 a1 x = share b0 b1 x → share a0 a1 y = share b0 b1 y → a0 = b0 ∧ a1 = b1 := by
  decide

/-- The reconstruction property in the form a participant cares about: two shares pin down the
    SECRET (the first component), for any two distinct participants. -/
theorem two_shares_determine_secret :
    ∀ a0 a1 b0 b1 x y : Fin 5, x ≠ y →
      share a0 a1 x = share b0 b1 x → share a0 a1 y = share b0 b1 y → a0 = b0 :=
  fun a0 a1 b0 b1 x y hxy h1 h2 => (two_shares_determine a0 a1 b0 b1 x y hxy h1 h2).1

/-! ### (2) Privacy: one share reveals nothing -/

/-- The five field elements, as the enumeration `decide` counts over. -/
abbrev gf5 : List (Fin 5) := List.finRange 5

/-- **One share excludes no secret.** For every participant point `x ≠ 0` and every value `y`
    that participant might hold, and for EVERY candidate secret `s`, exactly one coefficient
    `a1` makes `s` consistent with the observation — the count is `1`, the same for all five
    candidate secrets. A single share therefore rules nothing out; with `a1` uniform, the
    posterior over secrets equals the prior. -/
theorem one_share_reveals_nothing :
    ∀ x : Fin 5, x ≠ 0 → ∀ y s : Fin 5, gf5.countP (fun a1 => share s a1 x == y) = 1 := by
  decide

/-- The same fact stated as the comparison it licenses: for any two candidate secrets, a single
    share is consistent with both in exactly the same number of ways. This is the honest
    counting form of "the share's distribution does not depend on the secret". -/
theorem one_share_indistinguishable :
    ∀ x : Fin 5, x ≠ 0 → ∀ y s1 s2 : Fin 5,
      gf5.countP (fun a1 => share s1 a1 x == y) = gf5.countP (fun a1 => share s2 a1 x == y) := by
  intro x hx y s1 s2
  rw [one_share_reveals_nothing x hx y s1, one_share_reveals_nothing x hx y s2]

/-- **The threshold is exactly 2, not 1.** The contrast between the two results above is the
    whole point: two shares leave exactly one polynomial (`two_shares_determine`), one share
    leaves exactly one polynomial PER SECRET, i.e. five in all — so the second share is what
    collapses five possibilities to one. -/
theorem one_share_leaves_all_secrets_open :
    ∀ x : Fin 5, x ≠ 0 → ∀ y : Fin 5,
      (gf5.map (fun s => gf5.countP (fun a1 => share s a1 x == y))).sum = 5 := by
  decide

/-! ### Instance: a worked dealing -/

/-- Secret `3`, dealer's coefficient `4`: the four shares are `s(1) = 2`, `s(2) = 1`,
    `s(3) = 0`, `s(4) = 4`. Note `s(3) = 0` — a share may equal zero without revealing
    anything; it is the point `x = 0` that is withheld, not the value. -/
theorem worked_shares :
    share 3 4 1 = 2 ∧ share 3 4 2 = 1 ∧ share 3 4 3 = 0 ∧ share 3 4 4 = 4 := by decide

/-- All 25 candidate polynomials `(a0, a1)`. -/
abbrev polys : List (Fin 5 × Fin 5) :=
  gf5.flatMap (fun a0 => gf5.map (fun a1 => (a0, a1)))

/-- **Reconstruction, concretely.** Exactly one of the 25 candidate polynomials fits the two
    shares `s(1) = 2` and `s(3) = 0` — participants 1 and 3 pooling their shares recover the
    dealer's polynomial uniquely. -/
theorem worked_reconstruction :
    polys.countP (fun p => (share p.1 p.2 1 == 2) && (share p.1 p.2 3 == 0)) = 1 := by decide

/-- **Privacy, concretely.** Participant 1 alone (holding `s(1) = 2`) is left with five
    candidate polynomials — one for each of the five possible secrets. The share has excluded
    nothing. -/
theorem worked_privacy :
    polys.countP (fun p => share p.1 p.2 1 == 2) = 5 ∧
      gf5.countP (fun s => 0 < polys.countP (fun p => p.1 == s && share p.1 p.2 1 == 2)) = 5 := by
  decide

end AutoproverCorpus.ShamirThresholdGF5
