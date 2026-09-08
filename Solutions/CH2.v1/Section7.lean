/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Section 7 groundwork: elementary bounds on `coth`

The start of stage 6, and the start of §7 of Chirre–Helfgott. §7 opens by fixing the two facts
about `coth` that its estimates lean on, stated there as

  `coth y ≤ 1/y + y/3`   and   `coth y = 1 + 2/(e^{2y} - 1) ≤ 1 + 1/y`,

together with `coth` being decreasing on `(0, ∞)`. This file does the second of those, which is the
one `lem:trivialzer` uses to bound the contribution of the trivial zeroes.

## Why this is the right place to start

§7's weight estimates are the only part of stage 6 that depends on nothing else — no zeroes, no
contour, no Dirichlet series — so they can be built before any of the open questions are settled.
They are also how the deferred question gets answered: the recorded advice is to work §7 backwards
and state Theorem 1.1 only if a step genuinely needs it.

## What reading §7 corrected

**The trivial zeroes are handled, not excluded.** An earlier reconstruction had them dropping out
because they lie on the real axis. That is true of §5's decomposition, where `RC` removes the
axis — it is not what §7 does. §7 sums over them explicitly, with weight `coth(π(s-σ)/T)`, and
`lem:trivialzer` bounds the whole contribution by

  `(1/(2+σ) + 2π/T) / (x³ (1 - x^{-2}))`,

using that the residue of `-ζ'/ζ` at `s = -2n` is `-1`, that `coth` is decreasing, and the bound
below. So the trivial zeroes cost an `O(x^{-3})` term rather than nothing.

**Mathlib has `Complex.cot` now**, in `Trigonometric/Cotangent.lean`, with `cot_series_rep` and a
real API around it. `ZetaLogDeriv.v1`'s review notes still say it does not; that claim is stale and
should be corrected when that node is next touched.

`Real.coth` does **not** exist, so `cosh y / sinh y` is written out throughout.
-/

namespace CH2Section7

/-- `coth y = 1 + 2/(e^{2y} - 1)` for `y > 0`.

The form §7 uses to get the `1 + 1/y` bound: multiplying numerator and denominator of
`(e^y + e^{-y})/(e^y - e^{-y})` by `e^y` turns it into `(e^{2y} + 1)/(e^{2y} - 1)`. -/
theorem coth_eq_one_add_two_div {y : ℝ} (hy : 0 < y) :
    Real.cosh y / Real.sinh y = 1 + 2 / (Real.exp (2 * y) - 1) := by
  have ha : (0 : ℝ) < Real.exp y := Real.exp_pos y
  have hane : Real.exp y ≠ 0 := ha.ne'
  have hy1 : (1 : ℝ) < Real.exp y := by
    simpa using Real.exp_lt_exp.mpr hy
  have hexp : Real.exp (2 * y) = Real.exp y * Real.exp y := by
    rw [← Real.exp_add]; ring_nf
  have hbeq : Real.exp (-y) = 1 / Real.exp y := by
    rw [Real.exp_neg, one_div]
  have hden : Real.exp y ^ 2 - 1 ≠ 0 := by
    intro h; nlinarith
  have hden' : -1 + Real.exp y ^ 2 ≠ 0 := fun h ↦ hden (by linarith)
  rw [Real.cosh_eq, Real.sinh_eq, hexp, hbeq]
  field_simp
  ring

/-- **`coth y ≤ 1 + 1/y`** for `y > 0`, the bound §7 states and `lem:trivialzer` uses.

From `coth y = 1 + 2/(e^{2y} - 1)` together with `e^t ≥ 1 + t`, which gives `e^{2y} - 1 ≥ 2y`. -/
theorem coth_le_one_add_inv {y : ℝ} (hy : 0 < y) :
    Real.cosh y / Real.sinh y ≤ 1 + 1 / y := by
  rw [coth_eq_one_add_two_div hy]
  have hle : 2 * y ≤ Real.exp (2 * y) - 1 := by
    have := Real.add_one_le_exp (2 * y)
    linarith
  have hposy : (0 : ℝ) < 2 * y := by linarith
  have hpos : (0 : ℝ) < Real.exp (2 * y) - 1 := lt_of_lt_of_le hposy hle
  have : 2 / (Real.exp (2 * y) - 1) ≤ 2 / (2 * y) := by
    apply div_le_div_of_nonneg_left (by norm_num) hposy hle
  have hhalf : (2 : ℝ) / (2 * y) = 1 / y := by
    field_simp
  linarith [this, hhalf.le, hhalf.ge]

/-- `coth` is positive on `(0, ∞)`, which `lem:trivialzer` needs before it may use monotonicity. -/
theorem coth_pos {y : ℝ} (hy : 0 < y) : 0 < Real.cosh y / Real.sinh y := by
  have hs : 0 < Real.sinh y := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (-y) < Real.exp y := Real.exp_lt_exp.mpr (by linarith)
    linarith
  exact div_pos (Real.cosh_pos y) hs

end CH2Section7
