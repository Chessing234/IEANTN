/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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

/-! ### `h`, the series with non-negative coefficients

The move that makes part (c) tractable. `f(z) = 1/(πz) - cot πz` has Taylor coefficients
`(2/π) ζ(2n)`, positive but *not* decreasing fast enough for a crude bound; the paper instead
writes

  `f(z) = ((2/π) ζ(2) z - h(z)) / (1 - z²)`,   `h(z) = (2/π) ∑_{n≥1} aₙ z^{2n+1}`,

with `aₙ = ζ(2n) - ζ(2n+2) ≥ 0`. Multiplying the series by `1 - z²` telescopes it: all but the
leading term cancel in pairs, leaving the differences.

Two things are gained. `h` has a **closed form** — it is defined by one, here — so it can be
differentiated and evaluated by ordinary means. And its coefficients are non-negative, so
`|h(z)| ≤ h(‖z‖)`: a bound at one real point controls the whole disc, which is what turns the
two-dimensional maximum of `|A'|` over a rectangle into a one-dimensional evaluation. -/

/-- `f(z) = 1/(πz) - cot πz`, the function whose Taylor series `CotangentSeries.v1` supplies. -/
noncomputable def fcomp (z : ℂ) : ℂ :=
  1 / ((Real.pi : ℂ) * z) - Complex.cot ((Real.pi : ℂ) * z)

/-- The coefficients `aₙ = ζ(2n+2) - ζ(2n+4)`, in the index convention of `CotangentSeries.v1`.

The paper's `aₙ = ζ(2n) - ζ(2n+2)` for `n ≥ 1` is this at `n - 1`. -/
noncomputable def acoeff (n : ℕ) : ℝ :=
  zetaReal (2 * (n : ℝ) + 2) - zetaReal (2 * ((n : ℝ) + 1) + 2)

/-- **`aₙ ≥ 0`**, the whole point of the rearrangement. -/
theorem acoeff_nonneg (n : ℕ) : 0 ≤ acoeff n :=
  sub_nonneg.mpr (zetaReal_coeff_antitone n)

/-- `h(z) = (2/π) ζ(2) z - (1 - z²) f(z)`, defined by its closed form.

That the closed form has the advertised series is `hasSum_hcomp`; keeping the definition closed
means `h` may be differentiated and evaluated without ever touching the series. -/
noncomputable def hcomp (z : ℂ) : ℂ :=
  (2 / (Real.pi : ℂ)) * riemannZeta 2 * z - (1 - z ^ 2) * fcomp z

/-- **`h(z) = (2/π) ∑ aₙ z^{2n+3}`**, the telescoping.

`(1 - z²) f(z)` is the series minus its own shift by one place, so everything past the leading
`(2/π) ζ(2) z` collects into the differences `aₙ`. -/
theorem hasSum_hcomp
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {z : ℂ} (hz : z ≠ 0) (h1 : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ (2 / (Real.pi : ℂ)) * (acoeff n : ℂ) * z ^ (2 * n + 3)) (hcomp z) := by
  have H : HasSum (fun n : ℕ ↦ (2 / (Real.pi : ℂ)) * riemannZeta (2 * (n : ℂ) + 2)
      * z ^ (2 * n + 1)) (fcomp z) := hasSum_inv_pi_mul_sub_cot hcs hz h1
  -- multiply through by `z²`
  have S1 : HasSum (fun n : ℕ ↦ (2 / (Real.pi : ℂ)) * riemannZeta (2 * (n : ℂ) + 2)
      * z ^ (2 * n + 3)) (fcomp z * z ^ 2) := by
    have := H.mul_right (z ^ 2)
    refine this.congr_fun fun n ↦ ?_
    ring
  -- drop the leading term, which shifts the index by one
  set G : ℕ → ℂ := fun n ↦ (2 / (Real.pi : ℂ)) * riemannZeta (2 * (n : ℂ) + 2)
    * z ^ (2 * n + 1) with hG
  have S2 : HasSum (fun n : ℕ ↦ (2 / (Real.pi : ℂ)) * riemannZeta (2 * ((n : ℂ) + 1) + 2)
      * z ^ (2 * n + 3))
      (fcomp z - (2 / (Real.pi : ℂ)) * riemannZeta 2 * z) := by
    have hshift : HasSum (fun n : ℕ ↦ G (n + 1))
        (fcomp z - (2 / (Real.pi : ℂ)) * riemannZeta 2 * z) := by
      rw [hasSum_nat_add_iff 1]
      simpa [hG] using H
    refine hshift.congr_fun fun n ↦ ?_
    simp only [hG]
    push_cast
    ring
  have hval : fcomp z * z ^ 2 - (fcomp z - (2 / (Real.pi : ℂ)) * riemannZeta 2 * z)
      = hcomp z := by
    rw [hcomp]; ring
  rw [← hval]
  refine (S1.sub S2).congr_fun fun n ↦ ?_
  have e2 : riemannZeta (2 * (n : ℂ) + 2) = (zetaReal (2 * (n : ℝ) + 2) : ℂ) :=
    riemannZeta_coeff_ofReal n
  have e4 : riemannZeta (2 * ((n : ℂ) + 1) + 2) = (zetaReal (2 * ((n : ℝ) + 1) + 2) : ℂ) := by
    have := riemannZeta_coeff_ofReal (n + 1)
    push_cast at this ⊢
    convert this using 3
  rw [e2, e4, acoeff]
  push_cast
  ring

/-! ### The maximum of `|h|` on a disc is attained on the positive real axis

The consequence of `aₙ ≥ 0` that part (c) actually uses. Since every coefficient is non-negative,
the triangle inequality is an equality at a positive real argument:

  `|h(z)| ≤ (2/π) ∑ aₙ ‖z‖^{2n+3} = h(‖z‖)`.

So the two-dimensional maximum of `|A'|` over the rectangle `[0,½] × [-½,½]` is bounded by a
one-dimensional evaluation at `‖z‖ ≤ 1/√2`, the rectangle's furthest corner from the origin. -/

/-- `f` on the reals. -/
noncomputable def freal (r : ℝ) : ℝ := 1 / (Real.pi * r) - Real.cot (Real.pi * r)

/-- `h` on the reals, by the same closed form. -/
noncomputable def hreal (r : ℝ) : ℝ :=
  (2 / Real.pi) * zetaReal 2 * r - (1 - r ^ 2) * freal r

/-- `ζ(2)` as a real number, an instance of `riemannZeta_coeff_ofReal` at `n = 0`. -/
theorem riemannZeta_two_ofReal : riemannZeta 2 = (zetaReal 2 : ℂ) := by
  have h := riemannZeta_coeff_ofReal 0
  norm_num at h
  exact h

/-- `h` at a real point is the real `h`. -/
theorem hcomp_ofReal (r : ℝ) : hcomp (r : ℂ) = (hreal r : ℂ) := by
  have hcot : Complex.cot ((Real.pi : ℂ) * (r : ℂ)) = (Real.cot (Real.pi * r) : ℂ) := by
    rw [Complex.ofReal_cot]
    push_cast
    ring_nf
  rw [hcomp, hreal, fcomp, freal, riemannZeta_two_ofReal, hcot]
  push_cast
  ring

/-- The series for `h` at a real point of `(0,1)`, with real terms. -/
theorem hasSum_hreal
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasSum (fun n : ℕ ↦ (2 / Real.pi) * acoeff n * r ^ (2 * n + 3)) (hreal r) := by
  have hz : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hn : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
  have H := hasSum_hcomp hcs hz hn
  rw [hcomp_ofReal] at H
  rw [← Complex.hasSum_ofReal]
  refine H.congr_fun fun n ↦ ?_
  push_cast
  ring

/-- **`|h(z)| ≤ h(‖z‖)`.**

Non-negative coefficients, so the triangle inequality loses nothing at a positive real argument.
This is the step that makes the numerical bound a one-variable computation. -/
theorem norm_hcomp_le
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {z : ℂ} (hz : z ≠ 0) (h1 : ‖z‖ < 1) :
    ‖hcomp z‖ ≤ hreal ‖z‖ := by
  have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have H := hasSum_hcomp hcs hz h1
  have Hr := hasSum_hreal hcs hr0 h1
  have hterm : ∀ n : ℕ, ‖(2 / (Real.pi : ℂ)) * (acoeff n : ℂ) * z ^ (2 * n + 3)‖
      = (2 / Real.pi) * acoeff n * ‖z‖ ^ (2 * n + 3) := by
    intro n
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (acoeff_nonneg n)]
    congr 1
    rw [show (2 : ℂ) / (Real.pi : ℂ) = ((2 / Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsummable : Summable fun n : ℕ ↦ ‖(2 / (Real.pi : ℂ)) * (acoeff n : ℂ) * z ^ (2 * n + 3)‖ := by
    refine (Hr.summable).congr fun n ↦ (hterm n).symm
  calc ‖hcomp z‖ = ‖∑' n : ℕ, (2 / (Real.pi : ℂ)) * (acoeff n : ℂ) * z ^ (2 * n + 3)‖ := by
        rw [H.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖(2 / (Real.pi : ℂ)) * (acoeff n : ℂ) * z ^ (2 * n + 3)‖ :=
        norm_tsum_le_tsum_norm hsummable
    _ = hreal ‖z‖ := by
        rw [← Hr.tsum_eq]
        exact tsum_congr hterm

/-! ### `h'`, and the same disc bound for it

`A'` is built from `h` and `h'`, so the bound of the previous section is needed for the derivative
too. `h` is defined by a closed form, so `deriv hcomp` is an ordinary derivative; what has to be
established is that it is the termwise derivative of the series, and that is exactly what
`Complex.hasSum_deriv_of_summable_norm` gives — the terms are entire and uniformly bounded on a
disc of radius `R` with `‖z‖ < R < 1`.

The coefficients of `h'` are `(2n+3) aₙ`, still non-negative, so `|h'(z)| ≤ h'(‖z‖)` by the same
argument. -/

/-- `aₙ ≤ ζ(2)`, a crude bound, enough for summability of the differentiated series. -/
theorem acoeff_le_zetaReal_two (n : ℕ) : acoeff n ≤ zetaReal 2 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : zetaReal (2 * (n : ℝ) + 2) ≤ zetaReal 2 := by
    have := zetaReal_le (s := 2) (t := 2 * (n : ℝ) + 2) one_lt_two (by linarith)
    simpa using this
  have h2 : 0 ≤ zetaReal (2 * ((n : ℝ) + 1) + 2) := (zetaReal_pos (by linarith)).le
  rw [acoeff]
  linarith

/-- The differentiated series converges on `[0,1)`: `aₙ` is bounded and `∑ (2n+3) r^{2n+2}` is a
geometric series with a polynomial factor. -/
theorem summable_hderiv_terms {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ ↦ (2 / Real.pi) * acoeff n * (2 * (n : ℝ) + 3) * r ^ (2 * n + 2) := by
  have hs : ‖r ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  have g0 : Summable fun n : ℕ ↦ (n : ℝ) ^ 0 * (r ^ 2) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 0 hs
  have g1 : Summable fun n : ℕ ↦ (n : ℝ) ^ 1 * (r ^ 2) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hs
  have hmaj : Summable fun n : ℕ ↦ (2 / Real.pi) * zetaReal 2 * r ^ 2 *
      (2 * ((n : ℝ) ^ 1 * (r ^ 2) ^ n) + 3 * ((n : ℝ) ^ 0 * (r ^ 2) ^ n)) :=
    (((g1.mul_left 2).add (g0.mul_left 3)).mul_left _)
  refine Summable.of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) hmaj
  · have := acoeff_nonneg n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have : (0:ℝ) ≤ r ^ (2 * n + 2) := by positivity
    positivity
  · have hz2 : 0 < zetaReal 2 := zetaReal_pos one_lt_two
    have hpow : r ^ (2 * n + 2) = r ^ 2 * (r ^ 2) ^ n := by
      rw [← pow_mul]
      ring_nf
    have hnn : (0 : ℝ) ≤ (r ^ 2) ^ n := by positivity
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hpi : (0 : ℝ) < 2 / Real.pi := by positivity
    rw [hpow]
    have hcoef : (2 / Real.pi) * acoeff n * (2 * (n : ℝ) + 3)
        ≤ (2 / Real.pi) * zetaReal 2 * (2 * (n : ℝ) + 3) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (acoeff_le_zetaReal_two n) hpi.le) (by linarith)
    have hrhs : (2 / Real.pi) * zetaReal 2 * r ^ 2 *
        (2 * ((n : ℝ) ^ 1 * (r ^ 2) ^ n) + 3 * ((n : ℝ) ^ 0 * (r ^ 2) ^ n))
        = (2 / Real.pi) * zetaReal 2 * (2 * (n : ℝ) + 3) * (r ^ 2 * (r ^ 2) ^ n) := by
      simp only [pow_one, pow_zero, one_mul]
      ring
    rw [hrhs]
    have : (0:ℝ) ≤ r ^ 2 * (r ^ 2) ^ n := by positivity
    nlinarith [hcoef]

/-- `h'` on the reals, as the termwise derivative of the series for `h`. -/
noncomputable def hderivReal (r : ℝ) : ℝ :=
  ∑' n : ℕ, (2 / Real.pi) * acoeff n * (2 * (n : ℝ) + 3) * r ^ (2 * n + 2)

theorem hasSum_hderivReal {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ ↦ (2 / Real.pi) * acoeff n * (2 * (n : ℝ) + 3) * r ^ (2 * n + 2))
      (hderivReal r) :=
  (summable_hderiv_terms hr0 hr1).hasSum

/-- **The derivative of `h` is the termwise derivative of its series.**

The terms are entire and, on a disc of radius `R` with `‖z‖ < R < 1`, bounded by the summable
`(2/π) aₙ R^{2n+3}`; `Complex.hasSum_deriv_of_summable_norm` then differentiates under the sum.
The sum itself agrees with `hcomp` on the punctured disc, an open set containing `z`, so the two
derivatives agree. -/
theorem hasSum_deriv_hcomp
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {z : ℂ} (hz : z ≠ 0) (h1 : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ (2 / (Real.pi : ℂ)) * (acoeff n : ℂ) * ((2 * (n : ℝ) + 3 : ℝ) : ℂ)
      * z ^ (2 * n + 2)) (deriv hcomp z) := by
  set R : ℝ := (‖z‖ + 1) / 2 with hR
  have hzR : ‖z‖ < R := by rw [hR]; linarith
  have hR1 : R < 1 := by rw [hR]; linarith
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg z) hzR
  set F : ℕ → ℂ → ℂ := fun n w ↦ (2 / (Real.pi : ℂ)) * (acoeff n : ℂ) * w ^ (2 * n + 3) with hF
  have hu : Summable fun n : ℕ ↦ (2 / Real.pi) * acoeff n * R ^ (2 * n + 3) :=
    (hasSum_hreal hcs hR0 hR1).summable
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (F n) (Metric.ball (0 : ℂ) R) := by
    intro n
    exact (((differentiable_pow (2 * n + 3)).const_mul _)).differentiableOn
  have hle : ∀ (n : ℕ), ∀ w ∈ Metric.ball (0 : ℂ) R,
      ‖F n w‖ ≤ (2 / Real.pi) * acoeff n * R ^ (2 * n + 3) := by
    intro n w hw
    rw [mem_ball_zero_iff] at hw
    have hcast : ‖(2 / (Real.pi : ℂ)) * (acoeff n : ℂ)‖ = (2 / Real.pi) * acoeff n := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (acoeff_nonneg n),
        show (2 : ℂ) / (Real.pi : ℂ) = ((2 / Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hF]
    simp only [norm_mul, norm_pow]
    rw [show ‖(2 / (Real.pi : ℂ))‖ * ‖(acoeff n : ℂ)‖ = (2 / Real.pi) * acoeff n by
      rw [← norm_mul]; exact hcast]
    have hnn : (0:ℝ) ≤ (2 / Real.pi) * acoeff n := by
      have := acoeff_nonneg n; positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hw.le _) hnn
  have hmem : z ∈ Metric.ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; exact hzR
  have key := Complex.hasSum_deriv_of_summable_norm hu hdiff Metric.isOpen_ball hle hmem
  -- the sum agrees with `hcomp` on the punctured disc
  have hopen : IsOpen ({w : ℂ | w ≠ 0} ∩ Metric.ball (0 : ℂ) R) :=
    isOpen_ne.inter Metric.isOpen_ball
  have heq : (fun w : ℂ ↦ ∑' n : ℕ, F n w) =ᶠ[nhds z] hcomp := by
    filter_upwards [hopen.mem_nhds ⟨hz, hmem⟩] with w hw
    have hw1 : ‖w‖ < 1 := lt_trans (mem_ball_zero_iff.mp hw.2) hR1
    exact (hasSum_hcomp hcs hw.1 hw1).tsum_eq
  rw [← heq.deriv_eq]
  refine key.congr_fun fun n ↦ ?_
  have hd : HasDerivAt (F n)
      ((2 / (Real.pi : ℂ)) * (acoeff n : ℂ) * (((2 * n + 3 : ℕ) : ℂ) * z ^ (2 * n + 3 - 1))) z := by
    rw [hF]
    exact (hasDerivAt_pow (2 * n + 3) z).const_mul _
  rw [hd.deriv]
  have : 2 * n + 3 - 1 = 2 * n + 2 := by omega
  rw [this]
  push_cast
  ring

/-- **`|h'(z)| ≤ h'(‖z‖)`**, by the same non-negativity of the coefficients. -/
theorem norm_deriv_hcomp_le
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {z : ℂ} (hz : z ≠ 0) (h1 : ‖z‖ < 1) :
    ‖deriv hcomp z‖ ≤ hderivReal ‖z‖ := by
  have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have H := hasSum_deriv_hcomp hcs hz h1
  have Hr := hasSum_hderivReal hr0.le h1
  have hterm : ∀ n : ℕ, ‖(2 / (Real.pi : ℂ)) * (acoeff n : ℂ) * ((2 * (n : ℝ) + 3 : ℝ) : ℂ)
      * z ^ (2 * n + 2)‖ = (2 / Real.pi) * acoeff n * (2 * (n : ℝ) + 3) * ‖z‖ ^ (2 * n + 2) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (acoeff_nonneg n),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * (n : ℝ) + 3),
      show (2 : ℂ) / (Real.pi : ℂ) = ((2 / Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsummable : Summable fun n : ℕ ↦ ‖(2 / (Real.pi : ℂ)) * (acoeff n : ℂ)
      * ((2 * (n : ℝ) + 3 : ℝ) : ℂ) * z ^ (2 * n + 2)‖ :=
    (Hr.summable).congr fun n ↦ (hterm n).symm
  calc ‖deriv hcomp z‖
      = ‖∑' n : ℕ, (2 / (Real.pi : ℂ)) * (acoeff n : ℂ) * ((2 * (n : ℝ) + 3 : ℝ) : ℂ)
          * z ^ (2 * n + 2)‖ := by rw [H.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖(2 / (Real.pi : ℂ)) * (acoeff n : ℂ) * ((2 * (n : ℝ) + 3 : ℝ) : ℂ)
          * z ^ (2 * n + 2)‖ := norm_tsum_le_tsum_norm hsummable
    _ = hderivReal ‖z‖ := by rw [← Hr.tsum_eq]; exact tsum_congr hterm

/-! ### `h` and `h'` are increasing on `[0,1)`, and `h` is differentiable

Two loose ends before `A'` can be assembled. The disc bounds are in terms of `‖z‖`, and the
rectangle `[0,½] × [-½,½]` has `‖z‖ ≤ 1/√2`, so the bounds are only useful once `hreal` and
`hderivReal` are known to be increasing — which they are, termwise, because `aₙ ≥ 0`.

And `hcomp` must be differentiable before it has a derivative to speak of. Rather than
differentiate `cot`, this reuses the series: the sum is holomorphic on the disc by
`Complex.differentiableOn_tsum_of_summable_norm`, and it agrees with `hcomp` on the punctured disc,
which is a neighbourhood of every point of it. -/

theorem hreal_mono
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hs : s < 1) : hreal r ≤ hreal s := by
  have Hr := hasSum_hreal hcs hr (lt_of_le_of_lt hrs hs)
  have Hs := hasSum_hreal hcs (lt_of_lt_of_le hr hrs) hs
  rw [← Hr.tsum_eq, ← Hs.tsum_eq]
  refine Summable.tsum_le_tsum (fun n ↦ ?_) Hr.summable Hs.summable
  have hnn : (0:ℝ) ≤ (2 / Real.pi) * acoeff n := by
    have := acoeff_nonneg n; positivity
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrs _) hnn

theorem hderivReal_mono {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s < 1) :
    hderivReal r ≤ hderivReal s := by
  have Hr := hasSum_hderivReal hr (lt_of_le_of_lt hrs hs)
  have Hs := hasSum_hderivReal (hr.trans hrs) hs
  rw [← Hr.tsum_eq, ← Hs.tsum_eq]
  refine Summable.tsum_le_tsum (fun n ↦ ?_) Hr.summable Hs.summable
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnn : (0:ℝ) ≤ (2 / Real.pi) * acoeff n * (2 * (n : ℝ) + 3) := by
    have := acoeff_nonneg n
    have h3 : (0:ℝ) ≤ 2 * (n : ℝ) + 3 := by linarith
    positivity
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs _) hnn

/-- `hcomp` is differentiable on the punctured unit disc, by way of its series. -/
theorem differentiableAt_hcomp
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {z : ℂ} (hz : z ≠ 0) (h1 : ‖z‖ < 1) : DifferentiableAt ℂ hcomp z := by
  set R : ℝ := (‖z‖ + 1) / 2 with hR
  have hzR : ‖z‖ < R := by rw [hR]; linarith
  have hR1 : R < 1 := by rw [hR]; linarith
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg z) hzR
  set F : ℕ → ℂ → ℂ := fun n w ↦ (2 / (Real.pi : ℂ)) * (acoeff n : ℂ) * w ^ (2 * n + 3) with hF
  have hu : Summable fun n : ℕ ↦ (2 / Real.pi) * acoeff n * R ^ (2 * n + 3) :=
    (hasSum_hreal hcs hR0 hR1).summable
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (F n) (Metric.ball (0 : ℂ) R) :=
    fun n ↦ (((differentiable_pow (2 * n + 3)).const_mul _)).differentiableOn
  have hle : ∀ (n : ℕ), ∀ w ∈ Metric.ball (0 : ℂ) R,
      ‖F n w‖ ≤ (2 / Real.pi) * acoeff n * R ^ (2 * n + 3) := by
    intro n w hw
    rw [mem_ball_zero_iff] at hw
    have hcast : ‖(2 / (Real.pi : ℂ))‖ * ‖(acoeff n : ℂ)‖ = (2 / Real.pi) * acoeff n := by
      rw [← norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (acoeff_nonneg n),
        show (2 : ℂ) / (Real.pi : ℂ) = ((2 / Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hF]
    simp only [norm_mul, norm_pow]
    rw [hcast]
    have hnn : (0:ℝ) ≤ (2 / Real.pi) * acoeff n := by
      have := acoeff_nonneg n; positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hw.le _) hnn
  have hmem : z ∈ Metric.ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; exact hzR
  have hT : DifferentiableAt ℂ (fun w : ℂ ↦ ∑' n : ℕ, F n w) z :=
    ((Complex.differentiableOn_tsum_of_summable_norm hu hdiff Metric.isOpen_ball
      hle).differentiableAt (Metric.isOpen_ball.mem_nhds hmem))
  have hopen : IsOpen ({w : ℂ | w ≠ 0} ∩ Metric.ball (0 : ℂ) R) :=
    isOpen_ne.inter Metric.isOpen_ball
  have heq : (fun w : ℂ ↦ ∑' n : ℕ, F n w) =ᶠ[nhds z] hcomp := by
    filter_upwards [hopen.mem_nhds ⟨hz, hmem⟩] with w hw
    exact (hasSum_hcomp hcs hw.1 (lt_trans (mem_ball_zero_iff.mp hw.2) hR1)).tsum_eq
  exact hT.congr_of_eventuallyEq heq.symm

/-! ### `A'` in terms of `h` and `h'`

`(1+z) A(z) = h(z) - (2/π) ζ(2) z`, since `A(z) = -(1-z) f(z)` and
`h(z) = (2/π) ζ(2) z - (1-z²) f(z)`. Differentiating the quotient gives the paper's

  `A'(z) = -(2/π) ζ(2)/(1+z)² - h(z)/(1+z)² + h'(z)/(1+z)`,

which is the form the bound uses: `|1+z| ≥ 1` on the rectangle, so all three denominators help. -/

/-- `(1+z) A(z) = h(z) - (2/π) ζ(2) z` on the punctured unit disc. -/
theorem Acomp_eq_div {z : ℂ} (hz : z ≠ 0) (hz1 : (1 : ℂ) + z ≠ 0) :
    Acomp z = (hcomp z - (2 / (Real.pi : ℂ)) * riemannZeta 2 * z) / (1 + z) := by
  have hAf : Acomp z = -(1 - z) * fcomp z := by rw [Acomp_eq hz, fcomp]
  have hnum : hcomp z - (2 / (Real.pi : ℂ)) * riemannZeta 2 * z = (1 + z) * Acomp z := by
    rw [hcomp, hAf]; ring
  rw [hnum, mul_comm, mul_div_assoc, div_self hz1, mul_one]

/-- **`A'(z) = -(2/π) ζ(2)/(1+z)² - h(z)/(1+z)² + h'(z)/(1+z)`**, the paper's (cotaA').

Obtained from `(1+z) A(z) = h(z) - (2/π) ζ(2) z` by differentiating the quotient; `h` is
differentiable because its series is. This is the form the bound uses: `|1+z| ≥ 1` on the
rectangle, so all three denominators help rather than hurt. -/
theorem hasDerivAt_Acomp
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {z : ℂ} (hz : z ≠ 0) (h1 : ‖z‖ < 1) :
    HasDerivAt Acomp
      (-((2 / (Real.pi : ℂ)) * riemannZeta 2) / (1 + z) ^ 2 - hcomp z / (1 + z) ^ 2
        + deriv hcomp z / (1 + z)) z := by
  have hz1 : (1 : ℂ) + z ≠ 0 := by
    intro hcon
    have hzz : z = -1 := by linear_combination hcon
    rw [hzz] at h1
    simp at h1
  have hh : HasDerivAt hcomp (deriv hcomp z) z := (differentiableAt_hcomp hcs hz h1).hasDerivAt
  set c : ℂ := (2 / (Real.pi : ℂ)) * riemannZeta 2 with hcdef
  have hlin : HasDerivAt (fun w : ℂ ↦ c * w) c z := by
    simpa using (hasDerivAt_id z).const_mul c
  have hnum : HasDerivAt (fun w : ℂ ↦ hcomp w - c * w) (deriv hcomp z - c) z := hh.sub hlin
  have hden : HasDerivAt (fun w : ℂ ↦ 1 + w) 1 z := by
    simpa using (hasDerivAt_id z).const_add (1 : ℂ)
  have hQ : HasDerivAt (fun w : ℂ ↦ (hcomp w - c * w) / (1 + w))
      (((deriv hcomp z - c) * (1 + z) - (hcomp z - c * z) * 1) / (1 + z) ^ 2) z :=
    hnum.div hden hz1
  have heq : Acomp =ᶠ[nhds z] fun w : ℂ ↦ (hcomp w - c * w) / (1 + w) := by
    have hopen : IsOpen ({w : ℂ | w ≠ 0} ∩ Metric.ball (0 : ℂ) 1) :=
      isOpen_ne.inter Metric.isOpen_ball
    filter_upwards [hopen.mem_nhds ⟨hz, by rw [mem_ball_zero_iff]; exact h1⟩] with w hw
    have hw1 : (1 : ℂ) + w ≠ 0 := by
      intro hcon
      have hww : w = -1 := by linear_combination hcon
      have := mem_ball_zero_iff.mp hw.2
      rw [hww] at this
      simp at this
    exact Acomp_eq_div hw.1 hw1
  have hA := hQ.congr_of_eventuallyEq heq
  have hval : ((deriv hcomp z - c) * (1 + z) - (hcomp z - c * z) * 1) / (1 + z) ^ 2
      = -c / (1 + z) ^ 2 - hcomp z / (1 + z) ^ 2 + deriv hcomp z / (1 + z) := by
    field_simp
    ring
  rw [hval] at hA
  exact hA

/-! ### The bound on `|A'|` over the rectangle

Everything assembled. On `[0,½] × [-½,½]` two things hold: `‖z‖ ≤ 1/√2`, the corner furthest from
the origin, and `‖1+z‖ ≥ 1`, because `Re z ≥ 0`. So each of the three terms of `A'` is bounded by
its numerator, and each numerator by its value at `1/√2`.

What is left after this is one inequality between real numbers,
`(2/π) ζ(2) + h(1/√2) + h'(1/√2) < 1.78`, with nothing complex-analytic in it. -/

/-- `1/√2`, the corner of the rectangle furthest from the origin. -/
noncomputable def rcorner : ℝ := Real.sqrt (1 / 2)

theorem rcorner_sq : rcorner ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)

theorem rcorner_pos : 0 < rcorner := Real.sqrt_pos.mpr (by norm_num)

theorem rcorner_lt_one : rcorner < 1 := by nlinarith [rcorner_sq, rcorner_pos]

/-- `‖2ζ(2)/π‖ = 2ζ(2)/π`: the constant is a positive real. -/
theorem norm_const_zeta_two :
    ‖(2 / (Real.pi : ℂ)) * riemannZeta 2‖ = (2 / Real.pi) * zetaReal 2 := by
  rw [riemannZeta_two_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (zetaReal_pos one_lt_two),
    show (2 : ℂ) / (Real.pi : ℂ) = ((2 / Real.pi : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- **`|A'(z)| ≤ (2/π) ζ(2) + h(1/√2) + h'(1/√2)` on the rectangle** `[0,½] × [-½,½]`.

The paper's `1.77963…`; here still as three exact quantities, the numerical evaluation being a
separate matter. -/
theorem norm_deriv_Acomp_le
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {z : ℂ} (hz : z ≠ 0) (hx0 : 0 ≤ z.re) (hx : z.re ≤ 1 / 2) (hy : |z.im| ≤ 1 / 2) :
    ‖deriv Acomp z‖ ≤ (2 / Real.pi) * zetaReal 2 + hreal rcorner + hderivReal rcorner := by
  have him : z.im * z.im ≤ 1 / 4 := by
    have h := abs_nonneg z.im
    have : |z.im| * |z.im| ≤ (1 / 2) * (1 / 2) := mul_le_mul hy hy h (by norm_num)
    rw [abs_mul_abs_self] at this
    linarith
  have hnormsq : ‖z‖ ^ 2 ≤ 1 / 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have hnorm : ‖z‖ ≤ rcorner := by
    nlinarith [norm_nonneg z, rcorner_pos, rcorner_sq]
  have h1 : ‖z‖ < 1 := lt_of_le_of_lt hnorm rcorner_lt_one
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hden : (1 : ℝ) ≤ ‖1 + z‖ := by
    have hsq : (1 : ℝ) ≤ ‖1 + z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add]
      nlinarith
    nlinarith [norm_nonneg (1 + z)]
  have hden2 : (1 : ℝ) ≤ ‖1 + z‖ ^ 2 := one_le_pow₀ hden
  set c : ℂ := (2 / (Real.pi : ℂ)) * riemannZeta 2 with hcdef
  rw [(hasDerivAt_Acomp hcs hz h1).deriv]
  have hsplit : ‖-c / (1 + z) ^ 2 - hcomp z / (1 + z) ^ 2 + deriv hcomp z / (1 + z)‖
      ≤ ‖c‖ / ‖1 + z‖ ^ 2 + ‖hcomp z‖ / ‖1 + z‖ ^ 2 + ‖deriv hcomp z‖ / ‖1 + z‖ := by
    refine le_trans (norm_add_le _ _) ?_
    have h2 : ‖-c / (1 + z) ^ 2 - hcomp z / (1 + z) ^ 2‖
        ≤ ‖c‖ / ‖1 + z‖ ^ 2 + ‖hcomp z‖ / ‖1 + z‖ ^ 2 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_div, norm_div, norm_pow, norm_neg]
    rw [norm_div]
    have := norm_div (deriv hcomp z) (1 + z)
    linarith [h2]
  refine le_trans hsplit ?_
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
  have hb1 : ‖c‖ / ‖1 + z‖ ^ 2 ≤ (2 / Real.pi) * zetaReal 2 := by
    rw [← norm_const_zeta_two, ← hcdef]
    exact div_le_self hc0 hden2
  have hb2 : ‖hcomp z‖ / ‖1 + z‖ ^ 2 ≤ hreal rcorner :=
    le_trans (div_le_self (norm_nonneg _) hden2)
      (le_trans (norm_hcomp_le hcs hz h1) (hreal_mono hcs hz0 hnorm rcorner_lt_one))
  have hb3 : ‖deriv hcomp z‖ / ‖1 + z‖ ≤ hderivReal rcorner :=
    le_trans (div_le_self (norm_nonneg _) hden)
      (le_trans (norm_deriv_hcomp_le hcs hz h1)
        (hderivReal_mono hz0.le hnorm rcorner_lt_one))
  linarith

/-! ### Explicit values and lower bounds for `ζ`

The numerical half of part (c) needs `ζ(2)` and `ζ(4)` exactly — Mathlib has both — and *lower*
bounds on `ζ(6) - 1`, `ζ(8) - 1`, `ζ(10) - 1`. Lower bounds, not upper: the rearrangement below
turns the estimate into a series whose terms after the first are **negative**, so truncating it is
already an upper bound and each retained term wants its subtracted quantity as large as possible.

That is why no Bernoulli numbers appear here, and no tail estimate: a few terms of the Dirichlet
series suffice for each lower bound. -/

/-- Any partial sum of the Dirichlet series is a lower bound for `ζ`. -/
theorem sum_le_zetaReal {s : ℝ} (hs : 1 < s) (m : ℕ) :
    (∑ k ∈ Finset.range m, 1 / ((k : ℝ) + 1) ^ s) ≤ zetaReal s := by
  refine (summable_one_div_nat_add_one_rpow hs).sum_le_tsum _ (fun k _ ↦ by positivity)

/-- `ζ(2) = π²/6`. -/
theorem zetaReal_two_eq : zetaReal 2 = Real.pi ^ 2 / 6 := by
  have h : ((zetaReal 2 : ℝ) : ℂ) = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := by
    rw [← riemannZeta_two_ofReal, riemannZeta_two]
    push_cast
    ring
  exact_mod_cast h

/-- `ζ(4) = π⁴/90`. -/
theorem zetaReal_four_eq : zetaReal 4 = Real.pi ^ 4 / 90 := by
  have h : ((zetaReal 4 : ℝ) : ℂ) = (((Real.pi ^ 4 / 90 : ℝ)) : ℂ) := by
    rw [← zeta_ofReal (s := 4) (by norm_num)]
    norm_num [riemannZeta_four]
  exact_mod_cast h

/-- `ζ(6) - 1 ≥ 1/64 + 1/729 + 1/4096 + 1/15625`, four terms of the Dirichlet series. -/
theorem zetaReal_six_lower : (0.01730488 : ℝ) ≤ zetaReal 6 - 1 := by
  have h := sum_le_zetaReal (s := 6) (by norm_num) 5
  have hr : ∀ k : ℕ, ((k : ℝ) + 1) ^ (6 : ℝ) = ((k : ℝ) + 1) ^ (6 : ℕ) := by
    intro k
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hr] at h
  norm_num at h
  linarith

/-- `ζ(8) - 1 ≥ 1/256 + 1/6561`, two terms. -/
theorem zetaReal_eight_lower : (0.0040586 : ℝ) ≤ zetaReal 8 - 1 := by
  have h := sum_le_zetaReal (s := 8) (by norm_num) 3
  have hr : ∀ k : ℕ, ((k : ℝ) + 1) ^ (8 : ℝ) = ((k : ℝ) + 1) ^ (8 : ℕ) := by
    intro k
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hr] at h
  norm_num at h
  linarith

/-- `ζ(10) - 1 ≥ 1/1024`, one term. -/
theorem zetaReal_ten_lower : (0.00097656 : ℝ) ≤ zetaReal 10 - 1 := by
  have h := sum_le_zetaReal (s := 10) (by norm_num) 2
  have hr : ∀ k : ℕ, ((k : ℝ) + 1) ^ (10 : ℝ) = ((k : ℝ) + 1) ^ (10 : ℕ) := by
    intro k
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hr] at h
  norm_num at h
  linarith

/-! ### Abel summation, and why it removes the need for a tail estimate

`h(1/√2) + h'(1/√2) = (2/π) ∑ aₙ Wₙ` with `Wₙ = 2^{-(n+1)}(1/√2 + 2n + 3)`, and `aₙ` is the
difference `vₙ - vₙ₊₁` of `vₙ = ζ(2n+2) - 1`. Summing by parts,

  `∑ₙ (vₙ - vₙ₊₁) Wₙ = v₀ W₀ + ∑ₙ vₙ₊₁ (Wₙ₊₁ - Wₙ)`,

and `W` is decreasing while `v` is non-negative, so **every term after the first is `≤ 0`**.
Truncating the rearranged series is therefore already an upper bound — no tail has to be estimated,
and each retained term only needs a lower bound on some `ζ(2k) - 1`, which a handful of Dirichlet
terms supplies. This is what keeps `ζ(6)`, `ζ(8)`, `ζ(10)` and their Bernoulli numbers out of the
argument. -/

/-- `vₙ = ζ(2n+2) - 1`, the part of `ζ` past its leading term. -/
noncomputable def vcoeff (n : ℕ) : ℝ := zetaReal (2 * (n : ℝ) + 2) - 1

/-- `Wₙ = 2^{-(n+1)} (1/√2 + 2n + 3)`, the weight `h + h'` puts on `aₙ` at `z = 1/√2`. -/
noncomputable def wweight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1) * (rcorner + 2 * (n : ℝ) + 3)

theorem vcoeff_nonneg (n : ℕ) : 0 ≤ vcoeff n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have := one_le_zetaReal (s := 2 * (n : ℝ) + 2) (by linarith)
  rw [vcoeff]; linarith

theorem vcoeff_anti (n : ℕ) : vcoeff (n + 1) ≤ vcoeff n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have := zetaReal_le (s := 2 * (n : ℝ) + 2) (t := 2 * ((n : ℕ) + 1 : ℕ) + 2) (by linarith)
    (by push_cast; linarith)
  rw [vcoeff, vcoeff]
  linarith

theorem acoeff_eq_vcoeff_sub (n : ℕ) : acoeff n = vcoeff n - vcoeff (n + 1) := by
  rw [acoeff, vcoeff, vcoeff]
  push_cast
  ring

theorem wweight_pos (n : ℕ) : 0 < wweight n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have := rcorner_pos
  rw [wweight]
  positivity

/-- `Wₙ₊₁ - Wₙ = -2^{-(n+2)} (1/√2 + 2n + 1)`, so `W` is decreasing. -/
theorem wweight_succ_sub (n : ℕ) :
    wweight (n + 1) - wweight n = -((1 / 2 : ℝ) ^ (n + 2) * (rcorner + 2 * (n : ℝ) + 1)) := by
  rw [wweight, wweight, show n + 1 + 1 = n + 2 from rfl, pow_succ, pow_succ]
  push_cast
  ring

theorem wweight_le (n : ℕ) : wweight n ≤ (1 / 2 : ℝ) ^ (n + 1) * (2 * (n : ℝ) + 4) := by
  have h := rcorner_lt_one
  have hp : (0:ℝ) < (1 / 2 : ℝ) ^ (n + 1) := by positivity
  rw [wweight]
  exact mul_le_mul_of_nonneg_left (by linarith) hp.le

/-- The majorant for both halves of the summation by parts. -/
theorem summable_wmaj : Summable fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1) * (2 * (n : ℝ) + 4) := by
  have hs : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
  have g0 : Summable fun n : ℕ ↦ (n : ℝ) ^ 0 * (1 / 2 : ℝ) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 0 hs
  have g1 : Summable fun n : ℕ ↦ (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hs
  have := ((g1.mul_left 1).add (g0.mul_left 2))
  refine this.congr fun n ↦ ?_
  rw [pow_succ']
  simp only [pow_zero, one_mul]
  ring

theorem summable_vw : Summable fun n : ℕ ↦ vcoeff n * wweight n := by
  refine Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (vcoeff_nonneg n) (wweight_pos n).le)
    (fun n ↦ ?_) (summable_wmaj.mul_left (vcoeff 0))
  have hv : vcoeff n ≤ vcoeff 0 := by
    induction n with
    | zero => exact le_refl _
    | succ k ih => exact le_trans (vcoeff_anti k) ih
  exact mul_le_mul hv (wweight_le n) (wweight_pos n).le (vcoeff_nonneg 0)

theorem summable_vw' : Summable fun n : ℕ ↦ vcoeff (n + 1) * wweight n := by
  refine Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (vcoeff_nonneg _) (wweight_pos n).le)
    (fun n ↦ ?_) (summable_wmaj.mul_left (vcoeff 0))
  have hv : vcoeff (n + 1) ≤ vcoeff 0 := by
    induction n with
    | zero => exact vcoeff_anti 0
    | succ k ih => exact le_trans (vcoeff_anti (k + 1)) ih
  exact mul_le_mul hv (wweight_le n) (wweight_pos n).le (vcoeff_nonneg 0)

/-- `h(1/√2) + h'(1/√2) = (2/π) ∑ aₙ Wₙ`: the two series share a weight. -/
theorem hasSum_combined (hcs : CotangentSeries.v1.cot_series_zeta_values) :
    HasSum (fun n : ℕ ↦ (2 / Real.pi) * acoeff n * wweight n)
      (hreal rcorner + hderivReal rcorner) := by
  have H := (hasSum_hreal hcs rcorner_pos rcorner_lt_one).add
    (hasSum_hderivReal rcorner_pos.le rcorner_lt_one)
  refine H.congr_fun fun n ↦ ?_
  have hp : rcorner ^ (2 * n + 2) = (1 / 2 : ℝ) ^ (n + 1) := by
    rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul, rcorner_sq]
  have hp3 : rcorner ^ (2 * n + 3) = (1 / 2 : ℝ) ^ (n + 1) * rcorner := by
    rw [show 2 * n + 3 = (2 * n + 2) + 1 by ring, pow_succ, hp]
  rw [wweight, hp, hp3]
  ring

/-- **The summation by parts.** Every term of the rearranged series after the first is `≤ 0`, so
any partial sum of it is an upper bound. -/
theorem hreal_add_hderivReal_le_partial
    (hcs : CotangentSeries.v1.cot_series_zeta_values) (m : ℕ) :
    hreal rcorner + hderivReal rcorner ≤ (2 / Real.pi) * (vcoeff 0 * wweight 0
      + ∑ n ∈ Finset.range m, vcoeff (n + 1) * (wweight (n + 1) - wweight n)) := by
  set X : ℝ := ∑' n : ℕ, vcoeff n * wweight n with hX
  set Y : ℝ := ∑' n : ℕ, vcoeff (n + 1) * wweight n with hY
  have P : HasSum (fun n : ℕ ↦ vcoeff n * wweight n) X := summable_vw.hasSum
  have Q : HasSum (fun n : ℕ ↦ vcoeff (n + 1) * wweight n) Y := summable_vw'.hasSum
  have hcomb : hreal rcorner + hderivReal rcorner = (2 / Real.pi) * (X - Y) := by
    have H := hasSum_combined hcs
    have H2 : HasSum (fun n : ℕ ↦ (2 / Real.pi) * acoeff n * wweight n)
        ((2 / Real.pi) * (X - Y)) := by
      have := (P.sub Q).mul_left (2 / Real.pi)
      refine this.congr_fun fun n ↦ ?_
      rw [acoeff_eq_vcoeff_sub]
      ring
    exact H.unique H2
  have P' : HasSum (fun n : ℕ ↦ vcoeff (n + 1) * wweight (n + 1)) (X - vcoeff 0 * wweight 0) := by
    have := (hasSum_nat_add_iff (f := fun n : ℕ ↦ vcoeff n * wweight n) 1).mpr
      (show HasSum (fun n : ℕ ↦ vcoeff n * wweight n) (X - vcoeff 0 * wweight 0
        + ∑ i ∈ Finset.range 1, vcoeff i * wweight i) by simpa using P)
    exact this
  have D : HasSum (fun n : ℕ ↦ vcoeff (n + 1) * (wweight (n + 1) - wweight n))
      (X - vcoeff 0 * wweight 0 - Y) := by
    have := P'.sub Q
    refine this.congr_fun fun n ↦ ?_
    ring
  have hnonpos : ∀ n : ℕ, vcoeff (n + 1) * (wweight (n + 1) - wweight n) ≤ 0 := by
    intro n
    rw [wweight_succ_sub]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hr := rcorner_pos
    have : (0:ℝ) ≤ (1 / 2 : ℝ) ^ (n + 2) * (rcorner + 2 * (n : ℝ) + 1) := by positivity
    nlinarith [vcoeff_nonneg (n + 1)]
  have hle : X - vcoeff 0 * wweight 0 - Y
      ≤ ∑ n ∈ Finset.range m, vcoeff (n + 1) * (wweight (n + 1) - wweight n) := by
    have hneg := (D.neg).summable.sum_le_tsum (Finset.range m) (fun i _ ↦ by
      simpa using hnonpos i)
    rw [(D.neg).tsum_eq] at hneg
    simp only [Finset.sum_neg_distrib] at hneg
    linarith
  rw [hcomb]
  have hpi : (0:ℝ) < 2 / Real.pi := by positivity
  have : X - Y ≤ vcoeff 0 * wweight 0
      + ∑ n ∈ Finset.range m, vcoeff (n + 1) * (wweight (n + 1) - wweight n) := by linarith
  exact mul_le_mul_of_nonneg_left this hpi.le

/-! ### The numerical bound

Five terms of the rearranged series, with `π` pinned by `Real.pi_gt_3141592` and
`Real.pi_lt_3141593` and `1/√2` by its square. The true value of
`(2/π) ζ(2) + h(1/√2) + h'(1/√2)` is `1.7796360636…`, so the margin against `1.78` is `3.6·10⁻⁴`
and the arithmetic below has to be carried to about six places — which is why the bounds are
written out rather than left to a single call. -/

theorem vcoeff_zero : vcoeff 0 = Real.pi ^ 2 / 6 - 1 := by
  have h : (2 * ((0 : ℕ) : ℝ) + 2) = 2 := by norm_num
  rw [vcoeff, h, zetaReal_two_eq]

theorem vcoeff_one : vcoeff 1 = Real.pi ^ 4 / 90 - 1 := by
  have h : (2 * ((1 : ℕ) : ℝ) + 2) = 4 := by norm_num
  rw [vcoeff, h, zetaReal_four_eq]

theorem vcoeff_two_lower : (0.01730488 : ℝ) ≤ vcoeff 2 := by
  have h : (2 * ((2 : ℕ) : ℝ) + 2) = 6 := by norm_num
  rw [vcoeff, h]; exact zetaReal_six_lower

theorem vcoeff_three_lower : (0.0040586 : ℝ) ≤ vcoeff 3 := by
  have h : (2 * ((3 : ℕ) : ℝ) + 2) = 8 := by norm_num
  rw [vcoeff, h]; exact zetaReal_eight_lower

theorem vcoeff_four_lower : (0.00097656 : ℝ) ≤ vcoeff 4 := by
  have h : (2 * ((4 : ℕ) : ℝ) + 2) = 10 := by norm_num
  rw [vcoeff, h]; exact zetaReal_ten_lower

theorem rcorner_lower : (0.70710678 : ℝ) < rcorner := by nlinarith [rcorner_sq, rcorner_pos]

theorem rcorner_upper : rcorner < 0.70710679 := by nlinarith [rcorner_sq, rcorner_pos]

/-- The five retained terms, evaluated. `1.15059` is an upper bound for `1.1505556…`. -/
theorem bracket_le : vcoeff 0 * wweight 0
    + ∑ n ∈ Finset.range 4, vcoeff (n + 1) * (wweight (n + 1) - wweight n) ≤ 1.15059 := by
  have hr1 := rcorner_lower
  have hr2 := rcorner_upper
  have hpi1 : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi2 : Real.pi < 3.141593 := Real.pi_lt_d6
  have hsq1 : (9.8696 : ℝ) < Real.pi ^ 2 := by nlinarith
  have hsq2 : Real.pi ^ 2 < 9.86961 := by nlinarith
  have hq1 : (97.409 : ℝ) < Real.pi ^ 4 := by nlinarith [hsq1]
  have hv0hi : vcoeff 0 ≤ 0.644935 := by rw [vcoeff_zero]; linarith
  have hv0lo : (0 : ℝ) ≤ vcoeff 0 := vcoeff_nonneg 0
  have hv1lo : (0.0823222 : ℝ) ≤ vcoeff 1 := by rw [vcoeff_one]; linarith
  have hv2lo := vcoeff_two_lower
  have hv3lo := vcoeff_three_lower
  have hv4lo := vcoeff_four_lower
  -- the weights, evaluated
  have e0 : wweight 0 = (1 / 2 : ℝ) * (rcorner + 3) := by rw [wweight]; norm_num
  have e1 : wweight 1 - wweight 0 = -((1 / 4 : ℝ) * (rcorner + 1)) := by
    have h := wweight_succ_sub 0
    norm_num at h
    linarith
  have e2 : wweight 2 - wweight 1 = -((1 / 8 : ℝ) * (rcorner + 3)) := by
    have h := wweight_succ_sub 1
    norm_num at h
    linarith
  have e3 : wweight 3 - wweight 2 = -((1 / 16 : ℝ) * (rcorner + 5)) := by
    have h := wweight_succ_sub 2
    norm_num at h
    linarith
  have e4 : wweight 4 - wweight 3 = -((1 / 32 : ℝ) * (rcorner + 7)) := by
    have h := wweight_succ_sub 3
    norm_num at h
    linarith
  -- the five products
  have hp0 : vcoeff 0 * ((1 / 2 : ℝ) * (rcorner + 3)) ≤ 1.1954215 := by
    have hb : (1 / 2 : ℝ) * (rcorner + 3) ≤ 1.8535534 := by linarith
    have hbn : (0 : ℝ) ≤ (1 / 2 : ℝ) * (rcorner + 3) := by linarith
    have h := mul_le_mul hv0hi hb hbn (by norm_num : (0 : ℝ) ≤ 0.644935)
    norm_num at h
    linarith
  have hp1 : (0.0351331 : ℝ) ≤ vcoeff 1 * ((1 / 4 : ℝ) * (rcorner + 1)) := by
    have hb : (0.4267766 : ℝ) ≤ (1 / 4 : ℝ) * (rcorner + 1) := by linarith
    have h := mul_le_mul hv1lo hb (by norm_num : (0 : ℝ) ≤ (0.4267766 : ℝ))
      (by linarith : (0 : ℝ) ≤ vcoeff 1)
    norm_num at h
    linarith
  have hp2 : (0.0080188 : ℝ) ≤ vcoeff 2 * ((1 / 8 : ℝ) * (rcorner + 3)) := by
    have hb : (0.4633883 : ℝ) ≤ (1 / 8 : ℝ) * (rcorner + 3) := by linarith
    have h := mul_le_mul hv2lo hb (by norm_num : (0 : ℝ) ≤ (0.4633883 : ℝ))
      (by linarith : (0 : ℝ) ≤ vcoeff 2)
    norm_num at h
    linarith
  have hp3 : (0.0014476 : ℝ) ≤ vcoeff 3 * ((1 / 16 : ℝ) * (rcorner + 5)) := by
    have hb : (0.3566941 : ℝ) ≤ (1 / 16 : ℝ) * (rcorner + 5) := by linarith
    have h := mul_le_mul hv3lo hb (by norm_num : (0 : ℝ) ≤ (0.3566941 : ℝ))
      (by linarith : (0 : ℝ) ≤ vcoeff 3)
    norm_num at h
    linarith
  have hp4 : (0.0002352 : ℝ) ≤ vcoeff 4 * ((1 / 32 : ℝ) * (rcorner + 7)) := by
    have hb : (0.2408470 : ℝ) ≤ (1 / 32 : ℝ) * (rcorner + 7) := by linarith
    have h := mul_le_mul hv4lo hb (by norm_num : (0 : ℝ) ≤ (0.2408470 : ℝ))
      (by linarith : (0 : ℝ) ≤ vcoeff 4)
    norm_num at h
    linarith
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num only
  rw [e1, e2, e3, e4, e0]
  linarith

/-- **`(2/π) ζ(2) + h(1/√2) + h'(1/√2) ≤ 1.78`**, the paper's `1.77963…`. -/
theorem numeric_bound (hcs : CotangentSeries.v1.cot_series_zeta_values) :
    (2 / Real.pi) * zetaReal 2 + hreal rcorner + hderivReal rcorner ≤ 1.78 := by
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi1 : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi2 : Real.pi < 3.141593 := Real.pi_lt_d6
  have hsq2 : Real.pi ^ 2 < 9.86961 := by nlinarith
  have key := hreal_add_hderivReal_le_partial hcs 4
  have hstep : hreal rcorner + hderivReal rcorner ≤ (2 / Real.pi) * 1.15059 :=
    le_trans key (mul_le_mul_of_nonneg_left bracket_le (by positivity))
  have hz2 : (2 / Real.pi) * zetaReal 2 = Real.pi / 3 := by
    rw [zetaReal_two_eq]
    field_simp
    ring
  have hlast : (2 / Real.pi) * 1.15059 ≤ 1.78 - Real.pi / 3 := by
    rw [show (2 / Real.pi) * (1.15059 : ℝ) = (2 * 1.15059) / Real.pi by ring,
      div_le_iff₀ hpipos]
    nlinarith
  rw [hz2]
  linarith

/-- **`|A'(z)| ≤ 1.78` on the rectangle** `[0,½] × [-½,½]`, minus the origin.

The paper's `1.77963… < 1.78`. Everything of `lem:sibelius` (c) that is about `A'` ends here; what
remains is to integrate it. -/
theorem norm_deriv_Acomp_le_const
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {z : ℂ} (hz : z ≠ 0) (hx0 : 0 ≤ z.re) (hx : z.re ≤ 1 / 2) (hy : |z.im| ≤ 1 / 2) :
    ‖deriv Acomp z‖ ≤ 1.78 :=
  le_trans (norm_deriv_Acomp_le hcs hz hx0 hx hy) (numeric_bound hcs)

/-! ### Integrating the derivative bound: `|A(x+iy) - A(x)| ≤ 1.78 |y|`

The first half of `lem:sibelius` (c)'s conclusion. The mean value inequality is applied on the
**vertical segment** `{w | Re w = x, |Im w| ≤ ½}` rather than on the rectangle: the rectangle minus
the origin is not convex, and the segment is, while still avoiding the origin as long as `x > 0` —
which part (c) assumes anyway. -/

/-- On the rectangle, `‖z‖ ≤ 1/√2`. -/
theorem norm_le_rcorner {z : ℂ} (hx0 : 0 ≤ z.re) (hx : z.re ≤ 1 / 2) (hy : |z.im| ≤ 1 / 2) :
    ‖z‖ ≤ rcorner := by
  have him : z.im * z.im ≤ 1 / 4 := by
    have h := abs_nonneg z.im
    have h2 : |z.im| * |z.im| ≤ (1 / 2) * (1 / 2) := mul_le_mul hy hy h (by norm_num)
    rw [abs_mul_abs_self] at h2
    linarith
  have hnormsq : ‖z‖ ^ 2 ≤ 1 / 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  nlinarith [norm_nonneg z, rcorner_pos, rcorner_sq]

/-- The vertical segment through `x` inside the rectangle. -/
def vertSeg (x : ℝ) : Set ℂ := {w : ℂ | w.re = x ∧ |w.im| ≤ 1 / 2}

theorem convex_vertSeg (x : ℝ) : Convex ℝ (vertSeg x) := by
  intro a ha b hb u v hu hv huv
  refine ⟨?_, ?_⟩
  · have : (u • a + v • b).re = u * a.re + v * b.re := by simp
    rw [this, ha.1, hb.1, ← add_mul, huv, one_mul]
  · have him : (u • a + v • b).im = u * a.im + v * b.im := by simp
    rw [him]
    calc |u * a.im + v * b.im| ≤ |u * a.im| + |v * b.im| := abs_add_le _ _
      _ = u * |a.im| + v * |b.im| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg hv]
      _ ≤ u * (1 / 2) + v * (1 / 2) :=
          add_le_add (mul_le_mul_of_nonneg_left ha.2 hu) (mul_le_mul_of_nonneg_left hb.2 hv)
      _ = 1 / 2 := by rw [← add_mul, huv, one_mul]

/-- **`|A(x+iy) - A(x)| ≤ 1.78 |y|`** for `x ∈ (0,½]`, `|y| ≤ ½`. -/
theorem norm_Acomp_sub_le
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {x y : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) (hy : |y| ≤ 1 / 2) :
    ‖Acomp ((x : ℂ) + (y : ℂ) * Complex.I) - Acomp (x : ℂ)‖ ≤ 1.78 * |y| := by
  set S : Set ℂ := vertSeg x with hS
  have hmemA : (x : ℂ) ∈ S := by
    refine ⟨by simp, ?_⟩
    simp only [Complex.ofReal_im, abs_zero]
    norm_num
  have hmemB : (x : ℂ) + (y : ℂ) * Complex.I ∈ S := by
    refine ⟨by simp, ?_⟩
    simpa using hy
  have hbound : ∀ w ∈ S, ‖(ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv Acomp w))‖
      ≤ 1.78 := by
    intro w hw
    have hre : w.re = x := hw.1
    have hw0 : w ≠ 0 := by
      intro hcon
      rw [hcon] at hre
      simp at hre
      linarith [hre ▸ hx0]
    have hb := norm_deriv_Acomp_le_const hcs hw0 (by rw [hre]; linarith)
      (by rw [hre]; linarith) hw.2
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
    exact hb
  have hderiv : ∀ w ∈ S, HasFDerivWithinAt Acomp
      (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv Acomp w)) S w := by
    intro w hw
    have hre : w.re = x := hw.1
    have hw0 : w ≠ 0 := by
      intro hcon
      rw [hcon] at hre
      simp at hre
      linarith [hre ▸ hx0]
    have hnorm : ‖w‖ < 1 :=
      lt_of_le_of_lt (norm_le_rcorner (by rw [hre]; linarith) (by rw [hre]; linarith) hw.2)
        rcorner_lt_one
    have hd := hasDerivAt_Acomp hcs hw0 hnorm
    have hd' : HasDerivAt Acomp (deriv Acomp w) w := by rw [hd.deriv]; exact hd
    exact hd'.hasFDerivAt.hasFDerivWithinAt
  have key := (convex_vertSeg x).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hderiv hbound hmemA hmemB
  have hdist : ‖((x : ℂ) + (y : ℂ) * Complex.I) - (x : ℂ)‖ = |y| := by
    rw [show ((x : ℂ) + (y : ℂ) * Complex.I) - (x : ℂ) = (y : ℂ) * Complex.I by ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rwa [hdist] at key

/-! ### The second half of (c): `|A(x)| ≤ (π/3) x`

The paper reaches this through `A'(0) = -π/3` and the monotonicity of `A'` on `[0,½)`. The series
gives it directly, and on the whole of `(0,1)` rather than `[0,½]`:

  `-A(x) = (1-x) f(x) = (2/π) x · (1-x) ∑_{n≥0} ζ(2n+2) x^{2n}`,

so the claim is exactly `(1-x) ∑ ζ(2n+2) x^{2n} ≤ ζ(2)`, since `(2/π) ζ(2) = π/3`. Peeling off the
`n = 0` term leaves `(1-x) ∑_{n≥1} ζ(2n+2) x^{2n} ≤ ζ(2) x`, and there `ζ(2n+2) ≤ ζ(4)` and a
geometric series suffice: the left side is at most `ζ(4) x²/(1+x)`, and `ζ(4) ≤ ζ(2)` closes it.

Both signs come out of the same series: every coefficient is positive, so `f(x) > 0` and `A(x) < 0`
on `(0,1)`. -/

/-- `f` at a real point is the real `f`. -/
theorem fcomp_ofReal (x : ℝ) : fcomp (x : ℂ) = (freal x : ℂ) := by
  have hcot : Complex.cot ((Real.pi : ℂ) * (x : ℂ)) = (Real.cot (Real.pi * x) : ℂ) := by
    rw [Complex.ofReal_cot]
    push_cast
    ring_nf
  rw [fcomp, freal, hcot]
  push_cast
  ring

/-- The series for `f` at a real point of `(0,1)`. -/
theorem hasSum_freal
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ ↦ (2 / Real.pi) * zetaReal (2 * (n : ℝ) + 2) * x ^ (2 * n + 1))
      (freal x) := by
  have hz : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hn : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx1
  have H : HasSum (fun n : ℕ ↦ (2 / (Real.pi : ℂ)) * riemannZeta (2 * (n : ℂ) + 2)
      * (x : ℂ) ^ (2 * n + 1)) (fcomp (x : ℂ)) := hasSum_inv_pi_mul_sub_cot hcs hz hn
  rw [fcomp_ofReal] at H
  rw [← Complex.hasSum_ofReal]
  refine H.congr_fun fun n ↦ ?_
  rw [riemannZeta_coeff_ofReal]
  push_cast
  ring

theorem freal_pos
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : 0 < freal x := by
  have H := hasSum_freal hcs hx0 hx1
  have hterm : ∀ n : ℕ, (0 : ℝ) ≤ (2 / Real.pi) * zetaReal (2 * (n : ℝ) + 2) * x ^ (2 * n + 1) := by
    intro n
    have h1 : 0 < zetaReal (2 * (n : ℝ) + 2) := zetaReal_coeff_pos n
    have h2 : (0 : ℝ) < 2 / Real.pi := by positivity
    positivity
  have h0 := H.summable.le_tsum 0 (fun k _ ↦ hterm k)
  rw [H.tsum_eq] at h0
  have hpos : (0 : ℝ) < (2 / Real.pi) * zetaReal (2 * ((0 : ℕ) : ℝ) + 2) * x ^ (2 * 0 + 1) := by
    have h1 : 0 < zetaReal (2 * ((0 : ℕ) : ℝ) + 2) := zetaReal_coeff_pos 0
    have h2 : (0 : ℝ) < 2 / Real.pi := by positivity
    positivity
  linarith

/-- The series with the factor `(2/π) x` divided out: `G(x) = ∑ ζ(2n+2) x^{2n}`. -/
theorem hasSum_gseries
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ ↦ zetaReal (2 * (n : ℝ) + 2) * x ^ (2 * n))
      (Real.pi / (2 * x) * freal x) := by
  have H := (hasSum_freal hcs hx0 hx1).mul_left (Real.pi / (2 * x))
  refine H.congr_fun fun n ↦ ?_
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hx : x ≠ 0 := hx0.ne'
  rw [show x ^ (2 * n + 1) = x ^ (2 * n) * x from pow_succ x (2 * n)]
  field_simp

/-- **`(1-x) ∑ ζ(2n+2) x^{2n} ≤ ζ(2)`** on `(0,1)`: the tail is geometric with ratio `x²`. -/
theorem gseries_le
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (1 - x) * (Real.pi / (2 * x) * freal x) ≤ zetaReal 2 := by
  set G : ℝ := Real.pi / (2 * x) * freal x with hG
  have H := hasSum_gseries hcs hx0 hx1
  -- drop the leading term
  have hlead : zetaReal (2 * ((0 : ℕ) : ℝ) + 2) * x ^ (2 * 0) = zetaReal 2 := by norm_num
  have Hs : HasSum (fun n : ℕ ↦ zetaReal (2 * ((n : ℝ) + 1) + 2) * x ^ (2 * n + 2))
      (G - zetaReal 2) := by
    set F : ℕ → ℝ := fun n ↦ zetaReal (2 * (n : ℝ) + 2) * x ^ (2 * n) with hF
    have hshift : HasSum (fun n : ℕ ↦ F (n + 1)) (G - zetaReal 2) := by
      rw [hasSum_nat_add_iff 1]
      simpa [hF, hlead] using H
    refine hshift.congr_fun fun n ↦ ?_
    simp only [hF]
    push_cast
    ring
  -- the geometric majorant
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hx2n : (0 : ℝ) ≤ x ^ 2 := by positivity
  have Hgeo : HasSum (fun n : ℕ ↦ zetaReal 4 * x ^ 2 * (x ^ 2) ^ n)
      (zetaReal 4 * x ^ 2 * (1 - x ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one hx2n hx2).mul_left _
  have hle : G - zetaReal 2 ≤ zetaReal 4 * x ^ 2 * (1 - x ^ 2)⁻¹ := by
    rw [← Hs.tsum_eq, ← Hgeo.tsum_eq]
    refine Summable.tsum_le_tsum (fun n ↦ ?_) Hs.summable Hgeo.summable
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hz : zetaReal (2 * ((n : ℝ) + 1) + 2) ≤ zetaReal 4 := by
      have := zetaReal_le (s := 4) (t := 2 * ((n : ℝ) + 1) + 2) (by norm_num) (by linarith)
      exact this
    have hpow : x ^ (2 * n + 2) = x ^ 2 * (x ^ 2) ^ n := by
      rw [← pow_mul]
      ring_nf
    rw [hpow, mul_assoc]
    have hpn : (0 : ℝ) ≤ x ^ 2 * (x ^ 2) ^ n := by positivity
    exact mul_le_mul_of_nonneg_right hz hpn
  -- and the elementary inequality that finishes it
  have hz2 : 0 < zetaReal 2 := zetaReal_pos one_lt_two
  have hz4 : zetaReal 4 ≤ zetaReal 2 := zetaReal_le (by norm_num) (by norm_num)
  have hz4pos : 0 < zetaReal 4 := zetaReal_pos (by norm_num)
  have hfac : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  have hstep : (1 - x) * (zetaReal 4 * x ^ 2 * (1 - x ^ 2)⁻¹) ≤ zetaReal 2 * x := by
    rw [inv_eq_one_div, mul_one_div, ← mul_div_assoc, div_le_iff₀ hfac]
    have hfe : (1 - x ^ 2) = (1 - x) * (1 + x) := by ring
    rw [hfe]
    have h1 : (0 : ℝ) ≤ (1 - x) * x := by nlinarith
    have h2 : (0 : ℝ) ≤ zetaReal 2 - zetaReal 4 := by linarith
    nlinarith [mul_nonneg h1 hz2.le, mul_nonneg (mul_nonneg h1 hx0.le) h2]
  nlinarith [hle, hstep]

/-- **`|A(x)| ≤ (π/3) x` on `(0,1)`**, the remaining half of `lem:sibelius` (c).

Stronger than the paper's `[0,½]`: the series argument does not care where in `(0,1)` the point is,
and `(2/π) ζ(2) = π/3` is what makes the constant exactly `π/3`. -/
theorem norm_Acomp_real_le
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖Acomp (x : ℂ)‖ ≤ Real.pi / 3 * x := by
  have hz : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hAf : Acomp (x : ℂ) = ((-(1 - x) * freal x : ℝ) : ℂ) := by
    rw [Acomp_eq hz, show (1 / ((Real.pi : ℂ) * (x : ℂ)) - Complex.cot ((Real.pi : ℂ) * (x : ℂ)))
      = fcomp (x : ℂ) from rfl, fcomp_ofReal]
    push_cast
    ring
  have hfp := freal_pos hcs hx0 hx1
  have hnn : (0 : ℝ) ≤ (1 - x) * freal x := by nlinarith
  have hnorm : ‖Acomp (x : ℂ)‖ = (1 - x) * freal x := by
    rw [hAf, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by nlinarith)]
    ring
  rw [hnorm]
  have hG := gseries_le hcs hx0 hx1
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hexp : (1 - x) * freal x = 2 * x / Real.pi * ((1 - x) * (Real.pi / (2 * x) * freal x)) := by
    field_simp
  rw [hexp]
  have hcoef : (0 : ℝ) < 2 * x / Real.pi := by positivity
  calc 2 * x / Real.pi * ((1 - x) * (Real.pi / (2 * x) * freal x))
      ≤ 2 * x / Real.pi * zetaReal 2 := mul_le_mul_of_nonneg_left hG hcoef.le
    _ = 2 * x / Real.pi * (Real.pi ^ 2 / 6) := by rw [zetaReal_two_eq]
    _ = Real.pi / 3 * x := by field_simp; ring

/-! ### `lem:sibelius` (c), and the first case of (b)

Both halves of (c) in one place, and the consequence the paper draws immediately: for
`0 < x ≤ ½` the estimate (b) follows from (c) and nothing else, since `F = A + 1/(πz)` and

  `|1/(x+iy) - 1/x| = |y| / (x |x+iy|)`.

Only the remaining case `½ ≤ x ≤ 1` of (b) needs `lem:cothder` and Phragmén–Lindelöf. -/

/-- **`lem:sibelius` (c)**, both halves. -/
theorem sibelius_c
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {x y : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) (hy : |y| ≤ 1 / 2) :
    ‖Acomp (x : ℂ)‖ ≤ Real.pi / 3 * x ∧
      ‖Acomp ((x : ℂ) + (y : ℂ) * Complex.I) - Acomp (x : ℂ)‖ ≤ 1.78 * |y| :=
  ⟨norm_Acomp_real_le hcs hx0 (by linarith), norm_Acomp_sub_le hcs hx0 hx hy⟩

/-- **`lem:sibelius` (b) for `0 < x ≤ ½`**: `|F(x+iy) - F(x)| ≤ |y|/(πx|x+iy|) + 1.78|y|`.

`F = A + 1/(πz)`, so this is (c) plus one algebraic identity. -/
theorem norm_Fc_sub_le
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {x y : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) (hy : |y| ≤ 1 / 2) :
    ‖Fc ((x : ℂ) + (y : ℂ) * Complex.I) - Fc (x : ℂ)‖
      ≤ |y| / (Real.pi * x * ‖(x : ℂ) + (y : ℂ) * Complex.I‖) + 1.78 * |y| := by
  have ha0 : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hb0 : ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    intro hcon
    have hre : ((x : ℂ) + (y : ℂ) * Complex.I).re = 0 := by rw [hcon]; simp
    simp at hre
    linarith
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsplit : Fc ((x : ℂ) + (y : ℂ) * Complex.I) - Fc (x : ℂ)
      = (Acomp ((x : ℂ) + (y : ℂ) * Complex.I) - Acomp (x : ℂ))
        + (1 / ((Real.pi : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)) - 1 / ((Real.pi : ℂ) * (x : ℂ))) :=
    by rw [Acomp, Acomp]; ring
  have hdiff : 1 / ((Real.pi : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)) - 1 / ((Real.pi : ℂ) * (x : ℂ))
      = -((y : ℂ) * Complex.I)
        / ((Real.pi : ℂ) * (x : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)) := by
    field_simp
    ring
  have hnb : ‖(Real.pi : ℂ) * (x : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)‖
      = Real.pi * x * ‖(x : ℂ) + (y : ℂ) * Complex.I‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hx0]
  have hnn : ‖-((y : ℂ) * Complex.I)‖ = |y| := by
    rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc ‖Fc ((x : ℂ) + (y : ℂ) * Complex.I) - Fc (x : ℂ)‖
      = ‖(Acomp ((x : ℂ) + (y : ℂ) * Complex.I) - Acomp (x : ℂ))
          + (1 / ((Real.pi : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
            - 1 / ((Real.pi : ℂ) * (x : ℂ)))‖ := by rw [hsplit]
    _ ≤ ‖Acomp ((x : ℂ) + (y : ℂ) * Complex.I) - Acomp (x : ℂ)‖
          + ‖1 / ((Real.pi : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
            - 1 / ((Real.pi : ℂ) * (x : ℂ))‖ := norm_add_le _ _
    _ ≤ 1.78 * |y| + |y| / (Real.pi * x * ‖(x : ℂ) + (y : ℂ) * Complex.I‖) := by
        rw [hdiff, norm_div, hnn, hnb]
        linarith [norm_Acomp_sub_le hcs hx0 hx hy]
    _ = |y| / (Real.pi * x * ‖(x : ℂ) + (y : ℂ) * Complex.I‖) + 1.78 * |y| := by ring

/-! ### The other opening bound: `1/y ≤ coth y ≤ 1/y + y/3`

§7's preamble states this alongside `coth y ≤ 1 + 1/y`, and derives it from Euler's hyperbolic
expansion `coth y = 1/y + 2y ∑ 1/(y² + n²π²)` together with `∑ 1/(n²π²) = 1/6`.

**Proved here without the expansion.** Clearing denominators, the two claims are
`sinh y ≤ y cosh y` and `3y cosh y ≤ (3 + y²) sinh y`, and both follow from one differentiation
each: `ψ(y) = y cosh y - sinh y` has `ψ' = y sinh y`, and `φ(y) = (3+y²) sinh y - 3y cosh y` has
`φ' = y ψ(y)`. Both vanish at `0`. That is shorter than transporting a complex partial-fraction
identity onto the reals, and it avoids the interchange of limits that expansion needs. -/

/-- `ψ(y) = y cosh y - sinh y` is positive on `(0,∞)`; equivalently `tanh y < y`. -/
theorem mul_cosh_sub_sinh_pos {y : ℝ} (hy : 0 < y) : 0 < y * Real.cosh y - Real.sinh y := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ ↦ u * Real.cosh u - Real.sinh u)
      (1 * Real.cosh t + t * Real.sinh t - Real.cosh t) t := fun t ↦
    ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
  have hmono : StrictMonoOn (fun u : ℝ ↦ u * Real.cosh u - Real.sinh u) (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) (fun t _ ↦ ?_) (fun t ht ↦ ?_)
    · exact ((hderiv t).differentiableAt).continuousAt.continuousWithinAt
    · rw [interior_Ici] at ht
      rw [(hderiv t).deriv]
      have ht' : (0 : ℝ) < t := ht
      have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht'
      nlinarith [mul_pos ht' hs]
  have h : (0 : ℝ) * Real.cosh 0 - Real.sinh 0 < y * Real.cosh y - Real.sinh y :=
    hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy.le) hy
  simpa using h

/-- **`1/y ≤ coth y`** for `y > 0`. -/
theorem inv_le_coth {y : ℝ} (hy : 0 < y) : 1 / y ≤ Real.cosh y / Real.sinh y := by
  have hs : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy
  rw [div_le_div_iff₀ hy hs]
  nlinarith [mul_cosh_sub_sinh_pos hy]

/-- **`coth y ≤ 1/y + y/3`** for `y > 0`, the bound §7 gets from Euler's hyperbolic expansion. -/
theorem coth_le_inv_add_div_three {y : ℝ} (hy : 0 < y) :
    Real.cosh y / Real.sinh y ≤ 1 / y + y / 3 := by
  have hs : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy
  have hderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ ↦ (3 + u ^ 2) * Real.sinh u - 3 * u * Real.cosh u)
      (2 * t * Real.sinh t + (3 + t ^ 2) * Real.cosh t
        - (3 * Real.cosh t + 3 * t * Real.sinh t)) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ ↦ 3 + u ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).const_add (3 : ℝ)
    have h2 : HasDerivAt (fun u : ℝ ↦ Real.sinh u) (Real.cosh t) t := Real.hasDerivAt_sinh t
    have h3 : HasDerivAt (fun u : ℝ ↦ 3 * u) 3 t := by
      simpa using (hasDerivAt_id t).const_mul (3 : ℝ)
    have h4 : HasDerivAt (fun u : ℝ ↦ Real.cosh u) (Real.sinh t) t := Real.hasDerivAt_cosh t
    exact (h1.mul h2).sub (h3.mul h4)
  have hmono : StrictMonoOn
      (fun u : ℝ ↦ (3 + u ^ 2) * Real.sinh u - 3 * u * Real.cosh u) (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) (fun t _ ↦ ?_) (fun t ht ↦ ?_)
    · exact ((hderiv t).differentiableAt).continuousAt.continuousWithinAt
    · rw [interior_Ici] at ht
      rw [(hderiv t).deriv]
      have ht' : (0 : ℝ) < t := ht
      have hpsi := mul_cosh_sub_sinh_pos ht'
      nlinarith [mul_pos ht' hpsi]
  have hphi' : (3 + (0 : ℝ) ^ 2) * Real.sinh 0 - 3 * 0 * Real.cosh 0
      < (3 + y ^ 2) * Real.sinh y - 3 * y * Real.cosh y :=
    hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy.le) hy
  have hphi : (0 : ℝ) < (3 + y ^ 2) * Real.sinh y - 3 * y * Real.cosh y := by simpa using hphi'
  rw [div_add_div _ _ (ne_of_gt hy) (by norm_num : (3 : ℝ) ≠ 0), div_le_div_iff₀ hs (by positivity)]
  nlinarith

end CH2Section7
