/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Node `ZetaZeroes.v1`

Where the zeroes of `ζ` are, and how many. Six facts that every contour argument in explicit
analytic number theory reaches for, none of which Mathlib has.

## Why these are a node rather than a private step

They were proved inside `Solutions/CH2.v1` because a ladder argument needed them, and they are
stated here because nothing about them is specific to that paper. A contour that places vertical
columns at negative abscissas needs to know the trivial zeroes are the only ones out there; one
whose horizontal pieces must miss the zeroes needs an ordinate-free height; anything that sums over
zeroes needs them to be finite in a compact set, or the sum is a `tsum` of a non-summable family
and silently `0`.

## What Mathlib has, and where it stops

`riemannZeta_ne_zero_of_one_le_re` gives non-vanishing on `Re s ≥ 1`, and
`riemannZeta_neg_two_mul_nat_add_one` says each `-2(n+1)` *is* a zero. Between them there is
nothing: no statement that the trivial zeroes are the only ones in the left half-plane, no location
of the others, and no finiteness anywhere.

`riemannZeta₁` — `ζ` with its pole divided out, `riemannZeta₁ s = 1 + (s - 1) ζ₀ s` — is defined in
`Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean` for the asymptotic expansion and **is never related
back to `ζ`**. That bridge is what makes the zeroes isolated, since `riemannZeta₁` is entire and
not identically zero while `ζ` is not entire, and it is stated here for that reason.

## What is deliberately not here

**The residues of `ζ'/ζ`.** The residue at a zero is minus the multiplicity, and at `s = 1` it is
`1`; those are the facts a residue calculation actually consumes, and they belong beside these.
They are absent because Mathlib has no `residue` at all, and the one available in
`PrimeNumberTheoremAnd`'s port is labelled by its own authors a placeholder valid only for simple
poles. A conclusion resting on a placeholder attests to nothing. When they are added they should be
stated as limits — `(s - ρ) · (-ζ'/ζ)(s) → -m` as `s → ρ` — which is Mathlib-native and is what
consumers use anyway.

**Anything about the critical line.** `RiemannHypothesisUpTo` lives in Vocabulary and is a
hypothesis consumers carry; this node says where the zeroes are *unconditionally*.
-/

namespace ZetaZeroes.v1

/-- **The only zeroes of `ζ` in the left half-plane are the trivial ones.**

Mathlib has `riemannZeta_neg_two_mul_nat_add_one`, that each `-2(n+1)` is a zero, and
`riemannZeta_ne_zero_of_one_le_re` for `1 ≤ Re s`, but nothing that says the trivial zeroes are the
only ones out there. A ladder argument needs exactly that: it places its vertical columns at
negative abscissas and has to know they meet no zeroes.

The route is the functional equation and nothing else. Writing `s = 1 - w` with `Re w > 1`,
`riemannZeta_one_sub` expresses `ζ(s)` as a product of `2`, `(2π)^{-w}`, `Γ(w)`, `cos(πw/2)` and
`ζ(w)`; every factor but the cosine is nonzero for free, so `ζ(s) = 0` forces `cos(πw/2) = 0`,
hence `w = 2k+1` and `s = -2k`.

Imports nothing: `s` is universally quantified with every condition a hypothesis. -/
def no_nontrivial_zeroes_left : Prop :=
  ∀ s : ℂ, s.re < 0 → (∀ n : ℕ, s ≠ -2 * (n + 1)) → riemannZeta s ≠ 0

/-- **A zero off the real axis lies in the closed critical strip.**

The complement of `no_nontrivial_zeroes_left` together with Mathlib's non-vanishing on `Re s ≥ 1`:
to the right there are none, to the left the only ones are real, so anything with `Im ≠ 0` is
caught in `0 ≤ Re ≤ 1`. -/
def zeroes_off_axis_in_strip : Prop :=
  ∀ z : ℂ, riemannZeta z = 0 → z.im ≠ 0 → 0 ≤ z.re ∧ z.re ≤ 1

/-- **`ζ` has finitely many zeroes in any compact set missing `s = 1`.**

The workhorse, and the fact that makes a sum over zeroes mean anything: `zetaZeroesSum` is a `tsum`,
and a `tsum` of a non-summable family is `0`, so a zero-counting argument that never establishes
finiteness can be vacuously true.

`s = 1` must be excluded and the exclusion is not cosmetic — `ζ` has its pole there, so the
identity theorem cannot be applied to `ζ` on any set containing it. The proof goes through
`riemannZeta₁` instead, which is entire. -/
def finite_zeroes_on_compact : Prop :=
  ∀ K : Set ℂ, IsCompact K → (1 : ℂ) ∉ K → {z ∈ K | riemannZeta z = 0}.Finite

/-- **Every unit interval above the origin contains a height free of zero ordinates.**

What a contour needs when its horizontal pieces must miss the zeroes, and `T` is a free parameter
to be chosen. The argument is a counting one: a zero with `|Im z| ∈ [T₀, T₀+1]` is off the real
axis, hence in the closed critical strip, hence in a compact band missing the pole — of which there
are finitely many, and finitely many ordinates cannot exhaust an interval.

Note `|Im z|`, not `Im z`: a contour has two horizontal pieces and both must miss the zeroes, and
the zeroes are symmetric about the real axis anyway. -/
def exists_ordinate_free_height : Prop :=
  ∀ T₀ : ℝ, 0 < T₀ → ∃ T : ℝ, T₀ ≤ T ∧ T ≤ T₀ + 1 ∧
    ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ T

/-- **`ζ` is `riemannZeta₁` with the pole divided out**: `ζ s = riemannZeta₁ s / (s - 1)`.

Mathlib defines `riemannZeta₁` in `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean`, for the asymptotic
expansion, and never relates it back to `ζ`. Stated here because it is the bridge every argument
needs that wants to replace `ζ` by an entire function — which is to say every argument that wants
the identity theorem, since `ζ` has a pole and cannot be fed to it. -/
def zeta_eq_zeta1_div : Prop :=
  ∀ s : ℂ, s ≠ 1 → riemannZeta s = riemannZeta₁ s / (s - 1)

/-- **`ζ` and `riemannZeta₁` vanish at exactly the same points, away from `s = 1`.**

The form the bridge is usually used in. `CH2.v1` runs its whole ladder argument on
`-logDeriv riemannZeta₁` rather than on `-ζ'/ζ` precisely so that the identity theorem applies, and
this is what transfers zero facts between the two.

`s = 1` is excluded because `riemannZeta₁ 1 = 1 ≠ 0` while `ζ` has a pole there, so the two sides
say different things at that one point. -/
def zeta_eq_zero_iff_zeta1 : Prop :=
  ∀ s : ℂ, s ≠ 1 → (riemannZeta s = 0 ↔ riemannZeta₁ s = 0)

end ZetaZeroes.v1
