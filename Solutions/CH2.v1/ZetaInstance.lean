/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section5
import IEANTN.Nodes.ZetaLogDeriv.v1.Conclusions

/-!
# Instantiating §5 at `A(s) = -ζ'(s)/ζ(s)`

The first consumer of the ported §5 machinery, and the step that tells us whether that machinery is
*usable* rather than merely compiling.

Chirre–Helfgott's §10 (`prop:sagaro`) says what is wanted:

> Apply Theorem 1.1 with `A(s) = -ζ'(s)/ζ(s)`. The poles of `A(s)` are the zeros of `ζ(s)` and the
> pole of `ζ(s)` at `s = 1`. The residue of `A(s)` at a zero of `ζ(s)` is `-1` times the zero's
> multiplicity, and its residue at `s = 1` is `1`.

`prop_5_2` asks for five things about `F`. This file discharges the three that are properties of
`ζ` alone; the other two are growth bounds and belong with Appendix A. See the end of the file.

## The one that mattered

`HasSimplePolesOn` was the hypothesis I expected to be awkward — `−ζ'/ζ` has a pole at every zero of
`ζ`, of every multiplicity, and "simple pole regardless of multiplicity" is exactly the sort of fact
that is obvious on paper and painful in Lean. It is not painful: Mathlib has
`meromorphicOrderAt_logDeriv_eq_neg_one`, which says the logarithmic derivative has order exactly
`-1` at any zero or pole of a meromorphic function. A zero of order `m` gives `m/(s-ρ) + …`, order
`-1`, whatever `m` is.

That is worth recording because it also decides an earlier question: `ContourIntegration.v1`'s
general residue theorem, which admits arbitrary isolated singularities, is stronger than this
application ever needs.
-/

open Complex Filter Topology

namespace CH2ZetaInstance

/-- `A(s) = -ζ'(s)/ζ(s)`, the function CH2 applies the main theorem to.

Written as `-logDeriv riemannZeta` rather than `-(deriv ζ)/ζ` so that Mathlib's logarithmic
derivative API applies directly; the two are definitionally the same. -/
noncomputable def A : ℂ → ℂ := fun s ↦ -logDeriv riemannZeta s

/-- **Conjugation symmetry.** `A(s̄) = conj (A s)`, one of `prop_5_2`'s hypotheses.

Immediate from the ported `logDerivZeta_conj`, which is what `ZetaConj.lean` exists for. -/
lemma conjSymm_A : CH2.ConjSymm A := by
  intro s
  simp only [A, map_neg, neg_inj]
  exact logDerivZeta_conj' s

/-- `ζ` is analytic away from its pole.

`DifferentiableAt` unfolds to an `Exists`, so `(differentiableAt_riemannZeta hz).analyticAt` picks
up `Exists.analyticAt` and fails; the route is `DifferentiableOn.analyticAt` on the open complement
of `{1}`. -/
lemma analyticAt_riemannZeta {z : ℂ} (hz : z ∈ ({(1 : ℂ)}ᶜ : Set ℂ)) :
    AnalyticAt ℂ riemannZeta z := by
  refine DifferentiableOn.analyticAt (s := ({(1 : ℂ)}ᶜ : Set ℂ)) (fun w hw ↦ ?_) ?_
  · exact (differentiableAt_riemannZeta hw).differentiableWithinAt
  · exact (isOpen_compl_singleton).mem_nhds hz

/-- `ζ` is meromorphic away from its pole. -/
lemma meromorphicOn_riemannZeta_compl : MeromorphicOn riemannZeta {(1 : ℂ)}ᶜ :=
  fun z hz ↦ (analyticAt_riemannZeta hz).meromorphicAt

/-- **`A` is meromorphic away from `s = 1`.** -/
lemma meromorphicOn_A_compl : MeromorphicOn A {(1 : ℂ)}ᶜ := by
  have h := meromorphicOn_riemannZeta_compl.logDeriv
  intro z hz
  exact (h z hz).neg

/-! ### Closing the two gaps

`riemannZeta₀` and `riemannZeta₁` from `Mathlib.NumberTheory.Harmonic.ZetaAsymp` are what make this
work: `ζ s = (s-1)⁻¹ + riemannZeta₀ s` away from `1`, with `riemannZeta₀` **entire**. That gives
meromorphy at the pole directly, rather than through a removable-singularity argument.

The non-vanishing is then the identity theorem, which Mathlib has for meromorphic order:
`meromorphicOrderAt_ne_top_of_isPreconnected` transports "order `≠ ⊤`" across a preconnected set.
Seeding it at `s = 2`, where `ζ` is analytic and non-zero, gives it everywhere. -/

/-- `ζ` is meromorphic at its pole, via the entire function `riemannZeta₀`. -/
lemma meromorphicAt_riemannZeta_one : MeromorphicAt riemannZeta 1 := by
  have hEq : (fun s : ℂ ↦ (s - 1)⁻¹ + riemannZeta₀ s) =ᶠ[nhdsWithin 1 {(1 : ℂ)}ᶜ] riemannZeta := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (riemannZeta_eq_inv_sub_add hs).symm
  refine MeromorphicAt.congr ?_ hEq
  exact (((analyticAt_id.sub analyticAt_const).meromorphicAt).inv).add
    (DifferentiableOn.analyticAt differentiable_riemannZeta₀.differentiableOn
      Filter.univ_mem).meromorphicAt

/-- **`ζ` is meromorphic everywhere.** -/
lemma meromorphicOn_riemannZeta : MeromorphicOn riemannZeta Set.univ := by
  intro z _
  by_cases hz : z = 1
  · exact hz ▸ meromorphicAt_riemannZeta_one
  · exact (analyticAt_riemannZeta hz).meromorphicAt

/-- **`ζ` never vanishes identically near a point.**

The identity theorem, seeded at `s = 2` where `ζ` is analytic and non-zero. This discharges the
hypothesis the earlier version of `meromorphicOrderAt_A_ge_neg_one` had to carry. -/
lemma meromorphicOrderAt_riemannZeta_ne_top (z : ℂ) :
    meromorphicOrderAt riemannZeta z ≠ ⊤ := by
  have h2ne : riemannZeta 2 ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have h2an : AnalyticAt ℂ riemannZeta 2 := analyticAt_riemannZeta (by norm_num)
  have h2 : meromorphicOrderAt riemannZeta 2 ≠ ⊤ := by
    rw [h2an.meromorphicOrderAt_eq, h2an.analyticOrderAt_eq_zero.mpr h2ne]
    simp
  exact meromorphicOn_riemannZeta.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ 2) (Set.mem_univ z) h2

/-- **`HasSimplePolesOn A Set.univ`**, unconditionally — one of `prop_5_2`'s hypotheses, on the
whole plane rather than off the pole.

Note this includes `s = 1`: Mathlib's `meromorphicOrderAt_logDeriv_eq_neg_one` applies at poles as
well as zeros, and `ζ` has a simple pole there, so `A` has order `-1` at `1` too. -/
lemma hasSimplePolesOn_A_univ : HasSimplePolesOn A Set.univ := by
  intro z _
  have hζ : MeromorphicAt riemannZeta z := meromorphicOn_riemannZeta z (Set.mem_univ z)
  have hconst : meromorphicOrderAt (fun _ : ℂ ↦ (-1 : ℂ)) z = 0 := by
    rw [analyticAt_const.meromorphicOrderAt_eq, analyticAt_const.analyticOrderAt_eq_zero.mpr
      (by norm_num)]
    rfl
  have hAeq : A = (fun _ : ℂ ↦ (-1 : ℂ)) • logDeriv riemannZeta := by funext w; simp [A]
  have hA : meromorphicOrderAt A z = meromorphicOrderAt (logDeriv riemannZeta) z := by
    rw [hAeq, meromorphicOrderAt_smul analyticAt_const.meromorphicAt hζ.logDeriv, hconst, zero_add]
  rw [hA]
  by_cases h0 : meromorphicOrderAt riemannZeta z = 0
  · -- `ζ` neither vanishes nor blows up: the logarithmic derivative is regular.
    refine le_trans ?_ (meromorphicOrderAt_logDeriv_nonneg hζ h0)
    decide
  · rw [meromorphicOrderAt_logDeriv_eq_neg_one hζ h0 (meromorphicOrderAt_riemannZeta_ne_top z)]
    norm_cast

/-- **`A` is meromorphic everywhere.** -/
lemma meromorphicOn_A : MeromorphicOn A Set.univ := by
  intro z hz
  exact (meromorphicOn_riemannZeta.logDeriv z hz).neg

/-! ### Towards the two `IsBoundedNoPolesOn` hypotheses

`prop_5_2`'s remaining two hypotheses each ask for two separate things on
`l.Rboundary ∪ l.admissible_contour ∪ l.L` — that the function is bounded there, and that it has
no poles there. This section does the second half, which is where the ladder's abscissas are
actually chosen; the first half is a growth estimate and is not here. See `progress.yaml`.

The pole half reduces to knowing where `ζ` vanishes, because `A = -ζ'/ζ` has a pole exactly at a
zero or pole of `ζ` and is analytic elsewhere. On the ladder columns, which sit far to the left,
that needs a fact Mathlib does not have. -/

/-- **The only zeros of `ζ` in the left half-plane are the trivial ones.**

Mathlib has `riemannZeta_neg_two_mul_nat_add_one`, that each `-2(n+1)` *is* a zero, and
`riemannZeta_ne_zero_of_one_le_re` for `1 ≤ Re s`, but nothing that says the trivial zeros are the
only ones out there. A ladder argument needs exactly that: it places its vertical columns at
negative abscissas and has to know they meet no zeros.

The proof is the functional equation and nothing else. Writing `s = 1 - w` with `Re w > 1`,
`riemannZeta_one_sub` expresses `ζ(s)` as a product of `2`, `(2π)^{-w}`, `Γ(w)`, `cos(πw/2)` and
`ζ(w)`. Every factor but the cosine is nonzero for free — `Γ` never vanishes, and `ζ(w) ≠ 0`
because `Re w > 1` — so `ζ(s) = 0` forces `cos(πw/2) = 0`, hence `w = 2k+1` and `s = -2k`, and
`Re s < 0` makes `k` positive. That is the trivial zeros exactly.

Worth noting for anyone extending this: the same three Mathlib lemmas power
`ZetaLogDeriv.v1`'s solution, which is not a coincidence — both are the functional equation used
to move a fact from the convergent half-plane to the left one. -/
theorem riemannZeta_ne_zero_of_re_neg {s : ℂ} (hs : s.re < 0)
    (h : ∀ n : ℕ, s ≠ -2 * (n + 1)) : riemannZeta s ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨w, rfl⟩ : ∃ w : ℂ, s = 1 - w := ⟨1 - s, by ring⟩
  have hw : 1 < w.re := by simp only [Complex.sub_re, Complex.one_re] at hs; linarith
  have hwn : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    rw [hn] at hw
    simp only [Complex.neg_re, Complex.natCast_re] at hw
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hw1 : w ≠ 1 := by intro hn; rw [hn] at hw; simp at hw
  have hcos : Complex.cos ((Real.pi : ℂ) * w / 2) ≠ 0 := by
    rw [Ne, Complex.cos_eq_zero_iff]
    rintro ⟨k, hk⟩
    have h2 : (Real.pi : ℂ) * w = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by linear_combination 2 * hk
    have hwk : w = 2 * (k : ℂ) + 1 := mul_left_cancel₀ hpi h2
    have hkpos : 0 < k := by
      by_contra hk0
      push_neg at hk0
      rw [hwk] at hw
      simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
        Complex.one_re, Complex.re_ofNat, Complex.im_ofNat] at hw
      have : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
      linarith
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    exact h m (by rw [hwk]; push_cast; ring)
  rw [riemannZeta_one_sub hwn hw1]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) hcos) ?_
  · simp [Complex.cpow_eq_zero_iff, mul_ne_zero two_ne_zero hpi]
  · exact Complex.Gamma_ne_zero hwn
  · exact riemannZeta_ne_zero_of_one_lt_re hw

/-- **The ladder abscissas this instantiation uses: `σ n = 1 - 2n`.**

`LadderParams` leaves `σ` free, and the choice is the whole content of the pole half. Odd negative
abscissas are the classical choice and the reason is visible in
`riemannZeta_ne_zero_of_re_neg`: the trivial zeros are the *even* negative integers, so odd
columns thread between them. `σ 0 = 1` is forced by the structure, and `1 - 2n` is the simplest
sequence meeting that and decreasing to `-∞`. -/
noncomputable def sigmaZeta (n : ℕ) : ℝ := 1 - 2 * n

/-- Every ladder column past the first misses the zeros of `ζ`. -/
lemma riemannZeta_ne_zero_on_column {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z.re = sigmaZeta n) :
    riemannZeta z ≠ 0 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hre : z.re < 0 := by rw [hz]; simp only [sigmaZeta]; linarith
  refine riemannZeta_ne_zero_of_re_neg hre ?_
  intro m hm
  -- A trivial zero is real with even real part; the column's real part is odd.
  have : z.re = -2 * ((m : ℝ) + 1) := by rw [hm]; simp
  rw [hz] at this
  simp only [sigmaZeta] at this
  -- `1 - 2n = -2m - 2` has no solution in the naturals: the left side is odd, the right even.
  have hcast : (1 : ℝ) - 2 * n = -2 * m - 2 := by linarith
  have : (1 : ℤ) - 2 * n = -2 * m - 2 := by exact_mod_cast hcast
  omega

/-! ### The functional equation, in the orientation the ladder needs

`ZetaLogDeriv.v1` states

  `ζ'/ζ(w) = -ζ'/ζ(1-w) + log 2π - ψ(w) + (π/2) tan(π w / 2)`,

and read at `w = s` that is the *wrong* orientation for this argument: on a ladder column
`Re s ≤ -1`, it evaluates `ψ` at `s`, out in the left half-plane where `GammaAsymptotics.v1` says
nothing at all — its bound is stated for `Re w ≥ 1`.

Reading the same identity at `w = 1 - s` fixes that, and needs no new input. It moves `ψ` to
`1 - s`, where `Re (1-s) ≥ 2`, which is inside `GammaAsymptotics.v1`'s range. So the node is the
right one after all; it is the instantiation point that matters, and getting it wrong would have
sent someone looking for a digamma bound on the left half-plane, or for the reflection formula
that this repository's Mathlib pin does not yet carry.

Checked numerically at five points before being written, including `-9 + 5i`. -/
lemma logDeriv_ladder_form (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    {s : ℂ} (hs : s.re < 0)
    (hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) ≠ 0) :
    deriv riemannZeta s / riemannZeta s
      = -(deriv riemannZeta (1 - s) / riemannZeta (1 - s))
        + Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma (1 - s)
        + ((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * (1 - s) / 2) := by
  have hw : (1 : ℝ) < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hwn : ∀ n : ℕ, (1 - s) ≠ -n := by
    intro n hn
    rw [hn] at hw
    simp only [Complex.neg_re, Complex.natCast_re] at hw
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hw1 : (1 - s) ≠ 1 := by intro hn; rw [hn] at hw; simp at hw
  have hz : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw
  have h1 := hfe (1 - s) hwn hw1 hz hcos
  -- `1 - (1 - s)` is `s`; after that the identity is a rearrangement.
  rw [show (1 : ℂ) - (1 - s) = s by ring] at h1
  linear_combination h1

/-- On a ladder column the cosine factor never vanishes, so `logDeriv_ladder_form` applies there.

At `Re s = 1 - 2n` the reflected point is `1 - s = 2n - it`, and
`cos(π(2n - it)/2) = (-1)^n cosh(π t/2)`, which is bounded away from zero rather than merely
nonzero. Only the parity of `2n` is doing the work: an odd column would put the cosine's zeros on
the line. -/
lemma cos_ne_zero_on_column {n : ℕ} {s : ℂ} (hs : s.re = sigmaZeta n) :
    Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) ≠ 0 := by
  rw [Ne, Complex.cos_eq_zero_iff]
  rintro ⟨k, hk⟩
  -- Compare imaginary parts first: they force `s` real.
  have him : s.im = 0 := by
    have := congrArg Complex.im hk
    simp only [Complex.div_im, Complex.mul_im, Complex.mul_re, Complex.sub_im, Complex.sub_re,
      Complex.one_im, Complex.one_re, Complex.ofReal_im, Complex.ofReal_re, Complex.add_im,
      Complex.add_re, Complex.intCast_im, Complex.intCast_re, Complex.re_ofNat,
      Complex.im_ofNat, Complex.normSq_apply] at this
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith [this, hpi]
  -- Then real parts give `2n = 2k + 1`, which parity forbids.
  have hre := congrArg Complex.re hk
  simp only [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.normSq_apply, him, hs, sigmaZeta] at hre
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h2n : (2 : ℝ) * n = 2 * k + 1 := by field_simp at hre; nlinarith [hre, Real.pi_pos]
  have : (2 : ℤ) * n = 2 * k + 1 := by exact_mod_cast h2n
  omega

end CH2ZetaInstance
