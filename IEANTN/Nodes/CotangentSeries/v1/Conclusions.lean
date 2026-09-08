/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Node `CotangentSeries.v1`

The expansion of `π cot πz` in terms of `ζ(2n)`, which Mathlib does not have.

## What Mathlib has, and where it stops

`Trigonometric/Cotangent.lean` has Euler's partial fractions, `cot_series_rep`:
`π cot πz = 1/z + ∑ (1/(z-n) + 1/(z+n))`. `HurwitzZetaValues` has `riemannZeta_two_mul_nat`,
giving `ζ(2k)` in terms of Bernoulli numbers, and `NumberTheory/Bernoulli.lean` has the generating
function `t/(e^t - 1)`.

What is missing is the **Taylor expansion at the origin**,

  `π cot πz = 1/z - 2 ∑_{n≥1} ζ(2n) z^{2n-1}`,

which is the form every argument wants that needs the *coefficients* rather than the poles. The
two are equivalent by expanding each partial fraction geometrically and summing over `n` first,
but that interchange is the work, and nothing in Mathlib does it.

## Why it is a node

`CH2.v1` needs it in two places in §7 — for the Taylor series of `1/(πz) - cot πz` at `0`, and for
the sign of the coefficients `a_n = ζ(2n) - ζ(2n+2)` that the bound on `A'` rests on. Neither is
specific to that paper: this is the standard route to any coefficientwise estimate on the
cotangent, and to the classical `ζ(2n)` evaluations themselves.

Stating it here rather than inside a solution means the solution may assume it as a hypothesis
while it is proved separately, which is the point of the import mechanism.

## The shape of the statement

`HasSum` rather than an equation between `tsum`s, deliberately: a `tsum` of a non-summable family
is `0`, so an equation between them can hold vacuously. `HasSum` carries convergence with it.

The index is shifted so that `n : ℕ` starts at `0` and the summand is `2 ζ(2n+2) z^{2n+1}`, which
is the paper's `n ≥ 1` term at `n+1`. The hypotheses `z ≠ 0` and `‖z‖ < 1` are what keep `sin πz`
away from zero and the series inside its disc of convergence — the nearest poles of `cot πz` are at
`z = ±1`.
-/

namespace CotangentSeries.v1

/-- **`π cot πz = 1/z - 2 ∑_{n≥1} ζ(2n) z^{2n-1}` for `0 < ‖z‖ < 1`.**

Stated as a `HasSum` for the tail, so that convergence is part of the claim rather than something
a consumer must establish separately: the family `n ↦ 2 ζ(2n+2) z^{2n+1}` sums to
`1/z - π cot πz`.

Imports nothing: `z` is universally quantified with both conditions hypotheses, so a Lean proof is
the whole justification. -/
def cot_series_zeta_values : Prop :=
  ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 →
    HasSum (fun n : ℕ ↦ 2 * riemannZeta (2 * (n : ℂ) + 2) * z ^ (2 * n + 1))
      (1 / z - (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z))

end CotangentSeries.v1
