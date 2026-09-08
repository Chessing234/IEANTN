/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import IEANTN.Nodes.CotangentSeries.v1.Conclusions

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

/-! ### Towards `lem:sibelius`

`F(z) = 1/π - (1-z) cot(π(1-z))` is the function §7 compares the weights against, and
`lem:sibelius` is what it proves about it. Part (a) says `F` is decreasing on `(0,1]` with
`0 < F(x) < 1/(πx)`; parts (b) and (c) are perturbation bounds off the real axis.

This section does the upper bound of (a), which is the part that needs no series. The paper's
argument in one line: `cot π(1-x) = -cot πx`, so `F(x) = 1/π + (1-x) cot πx`, and
`cot πx < 1/(πx)` gives `F(x) < 1/π + (1-x)/(πx) = 1/(πx)`.

`F` is defined here on the reals. The complex `F` is what (b) and (c) need and comes with them. -/

/-- **`cot u < 1/u` on `(0, π)`.**

Equivalent to `u cos u < sin u` there, which splits at `π/2`: below it `lt_tan` gives
`u < tan u = sin u / cos u` with `cos u > 0`; at or above it `cos u ≤ 0` while `sin u > 0`, so the
inequality is immediate.

Mathlib has `lt_tan` and no cotangent counterpart; this looks like a reasonable addition there. -/
theorem cot_lt_inv {u : ℝ} (h0 : 0 < u) (hpi : u < Real.pi) : Real.cot u < 1 / u := by
  have hsin : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  rw [Real.cot_eq_cos_div_sin, div_lt_div_iff₀ hsin h0]
  rcases lt_or_ge u (Real.pi / 2) with h | h
  · have hcos : 0 < Real.cos u :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h⟩
    have htan := Real.lt_tan h0 h
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos] at htan
    nlinarith
  · have hcos : Real.cos u ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith [Real.pi_pos])
    nlinarith

/-- `cot (π - θ) = -cot θ`, from `sin (π - θ) = sin θ` and `cos (π - θ) = -cos θ`. -/
theorem cot_pi_sub (θ : ℝ) : Real.cot (Real.pi - θ) = -Real.cot θ := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.sin_pi_sub, Real.cos_pi_sub]
  ring

/-- The comparison function of §7, `F(z) = 1/π - (1-z) cot(π(1-z))`, on the reals. -/
noncomputable def Fweight (x : ℝ) : ℝ := 1 / Real.pi - (1 - x) * Real.cot (Real.pi * (1 - x))

/-- `F(x) = 1/π + (1-x) cot(πx)`, the form the estimates use. -/
theorem Fweight_eq (x : ℝ) :
    Fweight x = 1 / Real.pi + (1 - x) * Real.cot (Real.pi * x) := by
  have h : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring
  rw [Fweight, h, cot_pi_sub]
  ring

/-- **`lem:sibelius` (a), upper bound**: `F(x) < 1/(πx)` for `x ∈ (0,1)`.

The two factors of `1/(πx)` come from different places and add exactly: `1/π` from the constant
term, and `(1-x)/(πx)` from bounding `cot πx`, and `1/π + (1-x)/(πx) = 1/(πx)`. -/
theorem Fweight_lt_inv {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    Fweight x < 1 / (Real.pi * x) := by
  have hpi := Real.pi_pos
  have hpx0 : 0 < Real.pi * x := by positivity
  have hpxpi : Real.pi * x < Real.pi := by nlinarith
  have hcot : Real.cot (Real.pi * x) < 1 / (Real.pi * x) := cot_lt_inv hpx0 hpxpi
  have hsub : (0 : ℝ) < 1 - x := by linarith
  rw [Fweight_eq]
  have hmul : (1 - x) * Real.cot (Real.pi * x) < (1 - x) * (1 / (Real.pi * x)) :=
    mul_lt_mul_of_pos_left hcot hsub
  have hsum : 1 / Real.pi + (1 - x) * (1 / (Real.pi * x)) = 1 / (Real.pi * x) := by
    field_simp
    ring
  linarith

/-- **`lem:sibelius` (a), positivity**: `0 < F(x)` for `x ∈ (0,1)`.

The paper gets this from the expansion `F(z) = (2/π) Σₙ ζ(2n)(1-z)^{2n}`, whose coefficients are
positive. **Mathlib has no such expansion** — it has Euler's partial fractions (`cot_series_rep`)
and the Bernoulli generating function, but not `π cot πz = 1/z - 2 Σ ζ(2n) z^{2n-1}` — so that
route would have been a small project of its own.

It is not needed. Reading `F` in its original form `1/π - w cot(πw)` with `w = 1 - x`, positivity
is exactly `w cot(πw) < 1/π`, which is `cot_lt_inv` at `πw` multiplied by `w`. The same inequality
that gave the upper bound gives the lower one, at the reflected point. -/
theorem Fweight_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : 0 < Fweight x := by
  have hpi := Real.pi_pos
  have hw0 : (0 : ℝ) < 1 - x := by linarith
  have hwp : (0 : ℝ) < Real.pi * (1 - x) := by positivity
  have hw1 : Real.pi * (1 - x) < Real.pi := by nlinarith
  have hcot := cot_lt_inv hwp hw1
  have hmul : (1 - x) * Real.cot (Real.pi * (1 - x)) < (1 - x) * (1 / (Real.pi * (1 - x))) :=
    mul_lt_mul_of_pos_left hcot hw0
  have heq : (1 - x) * (1 / (Real.pi * (1 - x))) = 1 / Real.pi := by
    field_simp
  rw [Fweight]
  rw [heq] at hmul
  linarith

/-- **`u cot u` is strictly decreasing on `(0, π)`.**

The remaining half of `lem:sibelius` (a) reduces to this, and it too avoids the `ζ(2n)` expansion.
Differentiating, `(u cot u)' = (sin u cos u - u)/sin²u = (sin 2u - 2u)/(2 sin²u)`, which is
negative because `sin t < t` for `t > 0` — a fact Mathlib has as `Real.sin_lt`.

Stated as the derivative bound rather than as `StrictAntiOn`, because that is the form the
monotonicity argument consumes and it keeps the analytic content separate from the plumbing. -/
theorem deriv_mul_cot_neg {u : ℝ} (h0 : 0 < u) (hpi : u < Real.pi) :
    Real.sin u * Real.cos u - u < 0 := by
  have hsin2 : Real.sin (2 * u) = 2 * (Real.sin u * Real.cos u) := by
    rw [Real.sin_two_mul]; ring
  have hlt : Real.sin (2 * u) < 2 * u := Real.sin_lt (by linarith)
  linarith [hsin2 ▸ hlt]

/-- `cot' u = -1/sin²u` where `sin u ≠ 0`. Mathlib has no `Real.deriv_cot`, so it is derived from
the quotient rule and `sin² + cos² = 1`. -/
theorem hasDerivAt_cot {u : ℝ} (hs : Real.sin u ≠ 0) :
    HasDerivAt Real.cot (-(1 / Real.sin u ^ 2)) u := by
  have hq := (Real.hasDerivAt_cos u).div (Real.hasDerivAt_sin u) hs
  have hval : (-Real.sin u * Real.sin u - Real.cos u * Real.cos u) / Real.sin u ^ 2
      = -(1 / Real.sin u ^ 2) := by
    have hpy := Real.sin_sq_add_cos_sq u
    field_simp
    nlinarith [hpy]
  rw [hval] at hq
  have hfun : Real.cot = Real.cos / Real.sin := by
    funext x
    simp [Real.cot_eq_cos_div_sin, Pi.div_apply]
  rw [hfun]
  exact hq

/-- **`u cot u` is strictly decreasing on `(0, π)`**, the remaining analytic content of
`lem:sibelius` (a). -/
theorem strictAntiOn_mul_cot :
    StrictAntiOn (fun u : ℝ ↦ u * Real.cot u) (Set.Ioo 0 Real.pi) := by
  have hsin : ∀ u ∈ Set.Ioo (0 : ℝ) Real.pi, 0 < Real.sin u := fun u hu ↦
    Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2
  have hderiv : ∀ u ∈ Set.Ioo (0 : ℝ) Real.pi,
      HasDerivAt (fun t : ℝ ↦ t * Real.cot t)
        (1 * Real.cot u + u * -(1 / Real.sin u ^ 2)) u := fun u hu ↦
    (hasDerivAt_id u).mul (hasDerivAt_cot (hsin u hu).ne')
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) (fun u hu ↦ ?_) (fun u hu ↦ ?_)
  · exact ((hderiv u hu).differentiableAt).continuousAt.continuousWithinAt
  · rw [interior_Ioo] at hu
    rw [(hderiv u hu).deriv]
    have hs := hsin u hu
    have hnum := deriv_mul_cot_neg hu.1 hu.2
    have key : 1 * Real.cot u + u * -(1 / Real.sin u ^ 2)
        = (Real.sin u * Real.cos u - u) / Real.sin u ^ 2 := by
      rw [Real.cot_eq_cos_div_sin]
      field_simp
      ring
    rw [key]
    exact div_neg_of_neg_of_pos hnum (by positivity)

/-- **`lem:sibelius` (a), monotonicity**: `F` is strictly decreasing on `(0,1)`.

`F(x) = (1 - g(π(1-x)))/π` with `g u = u cot u`, so as `x` increases the argument `π(1-x)`
decreases, `g` of it increases, and `F` decreases.

**Stated on the open interval, where the paper says `(0,1]`, and the difference is a junk value
rather than a weakening.** `Real.cot 0 = cos 0 / sin 0 = 1/0 = 0` in Lean, so `Fweight 1 = 1/π` —
whereas the true limit of `F` at `1` is `0`. On `Ioc 0 1` the function would therefore *jump up* at
the endpoint and `StrictAntiOn` would be false. Any consumer wanting the closed interval must
either exclude `1` or carry the limit separately. -/
theorem strictAntiOn_Fweight : StrictAntiOn Fweight (Set.Ioo 0 1) := by
  intro a ha b hb hab
  have hpi := Real.pi_pos
  have hmem : ∀ x ∈ Set.Ioo (0 : ℝ) 1, Real.pi * (1 - x) ∈ Set.Ioo 0 Real.pi := by
    intro x hx
    constructor
    · have : (0 : ℝ) < 1 - x := by linarith [hx.2]
      positivity
    · nlinarith [hx.1]
  have hlt : Real.pi * (1 - b) < Real.pi * (1 - a) := by nlinarith
  have hg := strictAntiOn_mul_cot (hmem b hb) (hmem a ha) hlt
  -- `g (π(1-b)) > g (π(1-a))`, and `F = (1 - g)/π` reverses it once more.
  have hkey : Fweight a - Fweight b
      = (Real.pi * (1 - b) * Real.cot (Real.pi * (1 - b))
          - Real.pi * (1 - a) * Real.cot (Real.pi * (1 - a))) / Real.pi := by
    rw [Fweight, Fweight]
    field_simp
    ring
  have hpos : 0 < Fweight a - Fweight b := by
    rw [hkey]
    refine div_pos ?_ hpi
    simp only at hg
    linarith
  linarith

/-! ### The complex `F`, and why it is `s coth s` in disguise

Parts (b) and (c) of `lem:sibelius` are perturbation bounds off the real axis, so they need `F` as
a function on `ℂ`. Both proofs turn on one substitution, which is worth isolating because it
explains the shape of everything downstream.

Writing `s = iπ(1-z)`, so that `π(1-z) = -is`,

  `(1-z) cot(π(1-z)) = (s/(iπ)) · (i coth s) = (s coth s)/π`,

so `F(z) = (1 - s coth s)/π`. **`F` is `1 - s coth s` up to an affine change of variable**, which
is why `lem:cothder` — a statement about `(s coth s)'` — is what part (b) reaches for, and why the
bound it produces is `|F'(z)| ≤ |π(1-z)|`.
-/

/-- The comparison function of §7 as a function on `ℂ`. -/
noncomputable def Fc (z : ℂ) : ℂ :=
  1 / (Real.pi : ℂ) - (1 - z) * Complex.cot ((Real.pi : ℂ) * (1 - z))

/-- `F(z) = (1 - u cot u)/π` with `u = π(1-z)`: the constant and the product share a denominator. -/
theorem Fc_eq (z : ℂ) :
    Fc z = (1 - ((Real.pi : ℂ) * (1 - z)) * Complex.cot ((Real.pi : ℂ) * (1 - z)))
      / (Real.pi : ℂ) := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Fc]
  field_simp

/-- **`u cot u = s coth s` with `s = u i`.**

`cosh (u i) = cos u` and `sinh (u i) = (sin u) i`, so `coth (u i) = -i cot u` and the two factors
of `i` cancel. This is the substitution that turns every statement about `F` into one about
`s coth s`, and conversely — including `lem:cothder`, which part (b) uses to bound `F'`. -/
theorem mul_cot_eq_mul_coth (u : ℂ) :
    u * Complex.cot u
      = (u * Complex.I) * (Complex.cosh (u * Complex.I) / Complex.sinh (u * Complex.I)) := by
  rw [Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cot_eq_cos_div_sin]
  rcases eq_or_ne (Complex.sin u) 0 with h | h
  · simp [h]
  · field_simp

/-! ### The Taylor series part (c) works from

`lem:sibelius` (c) studies `A(z) = F(z) - 1/(πz)`, and its first move is to write
`A(z) = -(1-z) f(z)` with `f(z) = 1/(πz) - cot πz`, whose Taylor series at the origin is
`(2/π) ∑ ζ(2n) z^{2n-1}`.

That series is `CotangentSeries.v1`, imported rather than proved: it is classical, it is absent
from Mathlib, and it is not specific to this paper. Here it is divided through by `π` to land in
the form (c) uses. -/

/-- **The Taylor series of `f(z) = 1/(πz) - cot πz` at the origin**, from the imported expansion.

One division by `π` away from `CotangentSeries.v1.cot_series_zeta_values`, and the form
`lem:sibelius` (c) starts from. -/
theorem hasSum_inv_pi_mul_sub_cot
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {z : ℂ} (hz : z ≠ 0) (h1 : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ (2 / (Real.pi : ℂ)) * riemannZeta (2 * (n : ℂ) + 2) * z ^ (2 * n + 1))
      (1 / ((Real.pi : ℂ) * z) - Complex.cot ((Real.pi : ℂ) * z)) := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := hcs z hz h1
  have hval : (1 / z - (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z)) / (Real.pi : ℂ)
      = 1 / ((Real.pi : ℂ) * z) - Complex.cot ((Real.pi : ℂ) * z) := by
    field_simp
  have hfun :
      (fun n : ℕ ↦ (2 / (Real.pi : ℂ)) * riemannZeta (2 * (n : ℂ) + 2) * z ^ (2 * n + 1))
        = fun n : ℕ ↦ (2 * riemannZeta (2 * (n : ℂ) + 2) * z ^ (2 * n + 1)) / (Real.pi : ℂ) := by
    funext n
    ring
  rw [hfun, ← hval]
  exact h.div_const _

/-! ### Part (c): the function `A(z) = F(z) - 1/(πz)`

`lem:sibelius` (c) bounds `A` and its variation off the real axis. Its first move is to factor `A`
through the `f` whose Taylor series is now available:

  `A(z) = -(1-z) f(z)`,   `f(z) = 1/(πz) - cot πz`.

The factorisation is pure algebra once `cot π(1-z) = -cot πz` is available on `ℂ`, and it is what
turns a statement about `A` into one about a series with non-negative coefficients.

Part (b) needs this too: its case `0 < x ≤ 1/2` is (c) plus `|1/(x+iy) - 1/x| = |y|/(x|x+iy|)`.
Only the case `1/2 ≤ x ≤ 1` needs `lem:cothder` and Phragmén–Lindelöf. -/

/-- `cot (π - w) = -cot w` on `ℂ`. -/
theorem Complex.cot_pi_sub (w : ℂ) : Complex.cot ((Real.pi : ℂ) - w) = -Complex.cot w := by
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin]
  rw [show ((Real.pi : ℂ) - w) = ((Real.pi : ℝ) : ℂ) - w from rfl]
  rw [Complex.sin_pi_sub, Complex.cos_pi_sub]
  ring

/-- `F(z) = 1/π + (1-z) cot πz`, the reflected form. -/
theorem Fc_eq_add (z : ℂ) :
    Fc z = 1 / (Real.pi : ℂ) + (1 - z) * Complex.cot ((Real.pi : ℂ) * z) := by
  have h : (Real.pi : ℂ) * (1 - z) = (Real.pi : ℂ) - (Real.pi : ℂ) * z := by ring
  rw [Fc, h, Complex.cot_pi_sub]
  ring

/-- `A(z) = F(z) - 1/(πz)`, the object part (c) is about. -/
noncomputable def Acomp (z : ℂ) : ℂ := Fc z - 1 / ((Real.pi : ℂ) * z)

/-- **`A(z) = -(1-z) f(z)`** with `f(z) = 1/(πz) - cot πz`.

The two `1/(πz)` terms cancel against the constant `1/π`, which is why the factorisation is exact
rather than approximate. -/
theorem Acomp_eq {z : ℂ} (hz : z ≠ 0) :
    Acomp z = -(1 - z) * (1 / ((Real.pi : ℂ) * z) - Complex.cot ((Real.pi : ℂ) * z)) := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Acomp, Fc_eq_add]
  field_simp
  ring


/-! ### The Taylor coefficients are non-negative and decreasing

Part (c) is a bound on the whole disc extracted from the behaviour along one ray, and what licenses
that step is the sign of the coefficients: `f(z) = 1/(πz) - cot πz` has Taylor coefficients
`(2/π) ζ(2n+2)`, all positive, and the differences `ζ(2n+2) - ζ(2n+4)` are non-negative because
`ζ` decreases along the reals above `1`.

Mathlib has the Dirichlet series but **not** the monotonicity, so it is derived here termwise: each
`(k+1)^{-s}` decreases in the real exponent `s`, and the two sums may be compared because both
converge. The only friction is bookkeeping — `riemannZeta` lands in `ℂ` while the comparison is
real — so the value at a real point above `1` is first identified with a real `tsum`. -/

/-- The real Dirichlet series `∑_{k≥0} (k+1)^{-s}`, which is `ζ(s)` for `s > 1`.

Kept separate from `riemannZeta` so that the comparison below is between real numbers: `ℂ` has no
order, and `Summable.tsum_le_tsum` is what does the work. Outside `s > 1` this is a junk value —
the family is not summable there and the `tsum` is `0` — which is why every statement about it
carries `1 < s`. -/
noncomputable def zetaReal (s : ℝ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ s

/-- The `p`-series, shifted so that the first term is `1` rather than a division by zero. -/
theorem summable_one_div_nat_add_one_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun k : ℕ ↦ 1 / ((k : ℝ) + 1) ^ s := by
  have h := (Real.summable_one_div_nat_rpow (p := s)).mpr hs
  have h' := (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ) ^ s) 1).mpr h
  simpa using h'

/-- **`ζ` at a real point above `1` is the real Dirichlet sum.**

The bridge between `riemannZeta`, which is complex-valued, and the ordered setting the coefficient
comparison lives in. -/
theorem zeta_ofReal {s : ℝ} (hs : 1 < s) : riemannZeta (s : ℂ) = (zetaReal s : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs), zetaReal, Complex.ofReal_tsum]
  refine tsum_congr fun k ↦ ?_
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow hk]
  push_cast
  ring

/-- **`ζ` is antitone on the reals above `1`.**

Absent from Mathlib, and proved termwise: `(k+1)^{-s}` is decreasing in `s` because `k + 1 ≥ 1`, and
both series converge, so `Summable.tsum_le_tsum` applies. -/
theorem zetaReal_le {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) : zetaReal t ≤ zetaReal s := by
  refine Summable.tsum_le_tsum (fun k ↦ ?_)
    (summable_one_div_nat_add_one_rpow (hs.trans_le hst)) (summable_one_div_nat_add_one_rpow hs)
  have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpos : (0 : ℝ) < ((k : ℝ) + 1) ^ s := Real.rpow_pos_of_pos (by linarith) _
  exact one_div_le_one_div_of_le hpos (Real.rpow_le_rpow_of_exponent_le h1 hst)

/-- `1 ≤ ζ(s)` for real `s > 1`: the `k = 0` term is `1` and the rest are positive. -/
theorem one_le_zetaReal {s : ℝ} (hs : 1 < s) : 1 ≤ zetaReal s := by
  have h := (summable_one_div_nat_add_one_rpow hs).le_tsum 0 fun k _ ↦ by positivity
  simpa [zetaReal] using h

/-- `0 < ζ(s)` for real `s > 1`. -/
theorem zetaReal_pos {s : ℝ} (hs : 1 < s) : 0 < zetaReal s :=
  lt_of_lt_of_le zero_lt_one (one_le_zetaReal hs)

/-- The Taylor coefficient `ζ(2n+2)` of `CotangentSeries.v1`, identified as a real number. -/
theorem riemannZeta_coeff_ofReal (n : ℕ) :
    riemannZeta (2 * (n : ℂ) + 2) = (zetaReal (2 * (n : ℝ) + 2) : ℂ) := by
  have hs : (1 : ℝ) < 2 * (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hcast : ((2 * (n : ℝ) + 2 : ℝ) : ℂ) = 2 * (n : ℂ) + 2 := by push_cast; ring
  rw [← hcast, zeta_ofReal hs]

/-- **`aₙ = ζ(2n+2) - ζ(2n+4) ≥ 0`**, the sign the disc bound in part (c) rests on. -/
theorem zetaReal_coeff_antitone (n : ℕ) :
    zetaReal (2 * ((n : ℝ) + 1) + 2) ≤ zetaReal (2 * (n : ℝ) + 2) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact zetaReal_le (by linarith) (by linarith)

/-- The coefficients are positive: `0 < ζ(2n+2)`. -/
theorem zetaReal_coeff_pos (n : ℕ) : 0 < zetaReal (2 * (n : ℝ) + 2) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact zetaReal_pos (by linarith)

end CH2Section7
