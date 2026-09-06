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

/-- **`ζ'/ζ` is bounded on `Re w ≥ 2`**, from the Dirichlet series for `Λ`.

This is the bound `ZetaLogDeriv.v1`'s metadata deliberately declined to state as a node conclusion,
on the grounds that it is a short consequence of two facts Mathlib already has
(`LSeries_vonMangoldt_eq_deriv_riemannZeta_div` and `LSeriesSummable_vonMangoldt`) and would
therefore add an unjustified claim where none is needed. This is that consequence, and the
judgement holds up: it is a dozen lines.

The constant is `∑' n, ‖term Λ 2 n‖`, left unevaluated. Nothing here needs its value — only that
it is finite and independent of `w` — and pinning it to a decimal would invite exactly the
numerology the node avoided. The comparison across half-planes is
`LSeries.norm_term_le_of_re_le_re`, and the absolute convergence that lets the triangle inequality
through is `summable_norm_iff`, which applies because Mathlib's `Summable` is unconditional. -/
theorem logDeriv_riemannZeta_bounded_of_two_le_re :
    ∃ M : ℝ, ∀ w : ℂ, 2 ≤ w.re → ‖deriv riemannZeta w / riemannZeta w‖ ≤ M := by
  have hsum2 : Summable
      (fun n ↦ ‖LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖) :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
  refine ⟨∑' n, ‖LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖,
    fun w hw ↦ ?_⟩
  have h1 : 1 < w.re := by linarith
  have hle : ∀ n, ‖LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) w n‖
      ≤ ‖LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ := by
    intro n
    refine LSeries.norm_term_le_of_re_le_re _ ?_ n
    simpa using hw
  have hsumw : Summable
      (fun n ↦ ‖LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) w n‖) :=
    hsum2.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  have key : deriv riemannZeta w / riemannZeta w
      = -LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) w := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h1]; ring
  rw [key, norm_neg]
  calc ‖LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) w‖
      = ‖∑' n, LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) w n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) w n‖ :=
        norm_tsum_le_tsum_norm hsumw
    _ ≤ ∑' n, ‖LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ :=
        Summable.tsum_mono hsumw hsum2 hle

/-! ### Splitting the boundedness half into compact and unbounded pieces

`l.Rboundary ∪ l.admissible_contour ∪ l.L` is not compact — every piece of it runs off to
`Re s = -∞` — but it is a union of compact pieces and leftward rays, and the two need completely
different arguments. On a compact piece, analyticity is the whole story. On a ray, the growth of
`ζ'/ζ` matters and so does the `x₀ ^ s` decay that beats it.

This is the compact half, and it is worth having separately because three of the five pieces are
compact: the segment `{Re s = 1, |Im s| ≤ T}` of `∂R`, the contour's vertical stub
`{Re s = 1, Im s ∈ [0, δ]}`, and any bounded portion of a ray. -/

/-- **On a compact set where `f` is analytic, `IsBoundedNoPolesOn` is free.**

Both halves arrive at once and for different reasons. Analytic gives continuous, and a continuous
function on a compact set is bounded. Analytic also gives `meromorphicOrderAt ≥ 0` pointwise,
because the meromorphic order of an analytic function is its analytic order, which is a natural
number and so never negative.

Stated for a general `f` rather than for `A`: the same lemma serves `F`, `zOf · * F`, and each
multiplied by `x₀ ^ s`. -/
theorem isBoundedNoPolesOn_of_isCompact {f : ℂ → ℂ} {S : Set ℂ} (hS : IsCompact S)
    (hf : ∀ z ∈ S, AnalyticAt ℂ f z) : CH2.IsBoundedNoPolesOn f S := by
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn
    (fun z hz ↦ ((hf z hz).continuousAt).continuousWithinAt)
  refine ⟨M, fun z hz ↦ ⟨hM z hz, ?_⟩⟩
  rw [(hf z hz).meromorphicOrderAt_eq]
  exact ENat.map_natCast_nonneg

/-- The segment of `∂R` on the line `Re s = 1` is compact.

`{z | z.re = 1 ∧ |z.im| ≤ T}` is closed as an intersection of preimages of closed sets under the
continuous `re` and `im`, and bounded because both coordinates are. This is the piece of
`Rboundary` that carries `s = 1`, where `A` has its pole — so it is also the piece that forces the
whole argument to run on `F = A - 1/(s-1)` rather than on `A`. -/
lemma isCompact_reOne_segment (T : ℝ) : IsCompact {z : ℂ | z.re = 1 ∧ |z.im| ≤ T} := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · have h1 : IsClosed {z : ℂ | z.re = 1} :=
      isClosed_eq Complex.continuous_re continuous_const
    have h2 : IsClosed {z : ℂ | |z.im| ≤ T} :=
      isClosed_le (Complex.continuous_im.abs) continuous_const
    exact h1.inter h2
  · refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1 + |T|, fun z hz ↦ ?_⟩
    obtain ⟨hre, him⟩ := hz
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + |T| := by
          have hT : |z.im| ≤ |T| := him.trans (le_abs_self T)
          rw [hre]
          simp only [abs_one]
          linarith

/-! ### Isolation of the zeros, for choosing `T` and `δ`

`LadderParams` leaves `T` and `δ` free, and the ladder needs both off the zero ordinates: the
horizontal pieces `{Re s ≤ 1, |Im s| = T}` and `{Re s ≤ 1, Im s = δ}` must miss the zeros of `ζ`.
Nothing so far proves a good choice exists, and it is not free — it needs the zeros to be isolated.

The route is `riemannZeta₁`, and it is the right tool for a reason worth stating: the identity
theorem is about *analytic* functions, and `ζ` has a pole, so `ζ` itself cannot be fed to it on any
set containing `1`. Mathlib's `riemannZeta₁` is entire, and away from `1` it has exactly `ζ`'s
zeros. Mathlib does not currently connect the two — `riemannZeta₁` occurs only in `ZetaAsymp`,
where it was built for the asymptotic expansion — so the bridge is proved here. -/

/-- **`ζ` is `riemannZeta₁` with the pole divided out**: `ζ s = riemannZeta₁ s / (s - 1)`.

Immediate from `riemannZeta_eq_inv_sub_add` and the definition of `riemannZeta₁`, and apparently
absent from Mathlib, where `riemannZeta₁` is never related back to `ζ`. It is what makes that
helper usable for anything beyond the expansion it was introduced for. -/
theorem riemannZeta_eq_riemannZeta₁_div {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = riemannZeta₁ s / (s - 1) := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [riemannZeta_eq_inv_sub_add hs, riemannZeta₁]
  field_simp

/-- Away from the pole, the zeros of `ζ` are exactly the zeros of the entire `riemannZeta₁`. -/
theorem riemannZeta_eq_zero_iff_riemannZeta₁ {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = 0 ↔ riemannZeta₁ s = 0 := by
  rw [riemannZeta_eq_riemannZeta₁_div hs, div_eq_zero_iff]
  simp [sub_eq_zero, hs]

/-- The zeros of `riemannZeta₁` are isolated.

`riemannZeta₁` is entire and takes the value `1` at `s = 1`, so it is not identically zero and the
identity theorem applies on all of `ℂ` — no seed point has to be found, `riemannZeta₁_one` is one. -/
theorem riemannZeta₁_ne_zero_codiscrete :
    ∀ᶠ z in codiscreteWithin (Set.univ : Set ℂ), riemannZeta₁ z ≠ 0 := by
  have hana : AnalyticOnNhd ℂ riemannZeta₁ Set.univ := fun z _ ↦
    DifferentiableOn.analyticAt differentiable_riemannZeta₁.differentiableOn Filter.univ_mem
  rcases hana.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
  · exact absurd (h (Set.mem_univ 1)) (by simp [riemannZeta₁_one])
  · exact h

/-- **`ζ` has only finitely many zeros in a compact set avoiding the pole.**

This is what makes `T` and `δ` choosable: the ordinates occurring in any bounded band are finite,
so an interval of candidates contains one that is not an ordinate.

The pole has to be excluded, and excluding it is not a technicality — `ζ` is not analytic at `1`,
and `IsCompact.finite_sdiff_of_mem_codiscreteWithin` is applied to `riemannZeta₁`'s non-zero set,
which is codiscrete on all of `ℂ` precisely because `riemannZeta₁` is entire. For the ladder the
exclusion costs nothing: the bands in question have `|Im s|` bounded away from `0`. -/
theorem finite_zeros_riemannZeta_of_isCompact {K : Set ℂ} (hK : IsCompact K) (h1 : (1 : ℂ) ∉ K) :
    {z ∈ K | riemannZeta z = 0}.Finite := by
  have hmem : {z : ℂ | riemannZeta₁ z ≠ 0} ∈ codiscreteWithin K :=
    Filter.codiscreteWithin_mono (Set.subset_univ K) riemannZeta₁_ne_zero_codiscrete
  have hfin := hK.finite_sdiff_of_mem_codiscreteWithin hmem
  refine hfin.subset (fun z hz ↦ ?_)
  obtain ⟨hzK, hz0⟩ := hz
  refine ⟨hzK, ?_⟩
  simp only [Set.mem_setOf_eq, not_not]
  exact (riemannZeta_eq_zero_iff_riemannZeta₁ (fun h ↦ h1 (h ▸ hzK))).mp hz0

/-- Every zero of `ζ` off the real axis lies in the closed critical strip.

Both edges come from results already here: `riemannZeta_ne_zero_of_one_le_re` closes off
`Re z ≥ 1`, and `riemannZeta_ne_zero_of_re_neg` closes off `Re z < 0`, because the exceptions it
allows — the trivial zeros — are real, and this `z` is not. -/
lemma re_mem_Icc_of_riemannZeta_eq_zero {z : ℂ} (hz : riemannZeta z = 0) (him : z.im ≠ 0) :
    0 ≤ z.re ∧ z.re ≤ 1 := by
  constructor
  · by_contra hlt
    push_neg at hlt
    refine riemannZeta_ne_zero_of_re_neg hlt (fun n hn ↦ him ?_) hz
    rw [hn]; simp
  · by_contra hgt
    push_neg at hgt
    exact riemannZeta_ne_zero_of_one_le_re hgt.le hz

/-- The band of the critical strip at heights `|Im z| ∈ [T₀, T₀+1]` is compact.

No sign condition on `T₀` is needed; the band is compact whatever `T₀` is, and empty when it is
negative. Missing the pole is a separate fact, proved at the point of use. -/
lemma isCompact_strip_band (T₀ : ℝ) :
    IsCompact {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ T₀ ≤ |z.im| ∧ |z.im| ≤ T₀ + 1} := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · have hEq : {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ T₀ ≤ |z.im| ∧ |z.im| ≤ T₀ + 1}
        = {z : ℂ | 0 ≤ z.re} ∩ ({z : ℂ | z.re ≤ 1} ∩
            ({z : ℂ | T₀ ≤ |z.im|} ∩ {z : ℂ | |z.im| ≤ T₀ + 1})) := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [hEq]
    exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im.abs).inter
          (isClosed_le Complex.continuous_im.abs continuous_const)))
  · refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1 + (T₀ + 1), fun z hz ↦ ?_⟩
    obtain ⟨h0, h1, _, h3⟩ := hz
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + (T₀ + 1) := by
          have : |z.re| = z.re := abs_of_nonneg h0
          rw [this]
          linarith

/-- **A height free of zero ordinates exists in every unit interval above the real axis.**

This is what `LadderParams` needs and nothing so far supplied: `T` is a free parameter, and the
ladder's horizontal pieces must miss the zeros of `ζ`.

The argument is a counting one. A zero with `|Im z| ∈ [T₀, T₀+1]` is off the real axis, so it lies
in the closed critical strip, so it lies in a compact band missing the pole — of which there are
only finitely many. Finitely many ordinates cannot exhaust an interval. -/
theorem exists_ordinate_free_height {T₀ : ℝ} (hT₀ : 0 < T₀) :
    ∃ T, T₀ ≤ T ∧ T ≤ T₀ + 1 ∧ ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ T := by
  set K : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ T₀ ≤ |z.im| ∧ |z.im| ≤ T₀ + 1} with hK_def
  have h1K : (1 : ℂ) ∉ K := by
    simp only [hK_def, Set.mem_setOf_eq, Complex.one_im, abs_zero]
    rintro ⟨-, -, h, -⟩
    linarith
  have hfin := finite_zeros_riemannZeta_of_isCompact (isCompact_strip_band T₀) h1K
  -- The ordinates occurring in the band are finite; the candidates are not.
  have himg : ((fun z : ℂ ↦ |z.im|) '' {z ∈ K | riemannZeta z = 0}).Finite := hfin.image _
  have hinf : (Set.Icc T₀ (T₀ + 1)).Infinite := Set.Icc_infinite (by linarith)
  obtain ⟨T, hT⟩ := (hinf.diff himg).nonempty
  obtain ⟨hTmem, hTnot⟩ := hT
  refine ⟨T, hTmem.1, hTmem.2, fun z hz heq ↦ hTnot ⟨z, ⟨?_, hz⟩, heq⟩⟩
  -- `z` is a zero at height `T > 0`, hence off the axis, hence in the band.
  have him : z.im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at heq
    linarith [hTmem.1]
  obtain ⟨hre0, hre1⟩ := re_mem_Icc_of_riemannZeta_eq_zero hz him
  exact ⟨hre0, hre1, heq ▸ hTmem.1, heq ▸ hTmem.2⟩

/-! ### `F`, the function `prop_5_2` is actually applied to

`prop_5_2` is not applied to `A` but to Theorem 1.1's `F(s) = A(s) - Res_{s=1} A / (s-1)`, and the
reason is forced rather than stylistic: `l.Rboundary` **contains `s = 1`** — it has `Re s = 1` and
`|Im s| = 0 ≤ T` — while `IsBoundedNoPolesOn` demands `meromorphicOrderAt ≥ 0` there, which `A`
fails at its own pole. `A` cannot be the input.

`riemannZeta₁` makes `F` pleasant rather than awkward. From `ζ s = riemannZeta₁ s / (s - 1)`,
taking logarithmic derivatives,

  `A = -ζ'/ζ = -riemannZeta₁'/riemannZeta₁ + 1/(s-1)`,

so `F = A - 1/(s-1) = -logDeriv riemannZeta₁`. `F` is the logarithmic derivative of an **entire**
function, and `riemannZeta₁ 1 = 1 ≠ 0`, so `F` is analytic at the very point `A` was not.

A WARNING FOR WHOEVER CONTINUES. The three hypotheses recorded above as done -- `ConjSymm`,
`MeromorphicOn`, `HasSimplePolesOn` -- were proved for `A`, and `prop_5_2` wants them for `F`.
They do not transfer for free, they have to be reproved. That is not the setback it sounds like:
each is the same argument run on `riemannZeta₁`, which being entire is *easier* to work with than
`ζ`. Only `ConjSymm F` needs anything new, namely that `riemannZeta₁` commutes with conjugation. -/

/-- **`F = -logDeriv riemannZeta₁`**, Theorem 1.1's pole-free part of `A`.

Defined through `riemannZeta₁` rather than as the literal difference `A s - (s-1)⁻¹`, because the
two agree and this form is manifestly analytic wherever `riemannZeta₁` is non-zero — including at
`s = 1`, which is the whole point of introducing `F`. -/
noncomputable def F : ℂ → ℂ := fun s ↦ -logDeriv riemannZeta₁ s

/-- `riemannZeta₁` is entire, in the form the analytic API wants. -/
lemma analyticAt_riemannZeta₁ (z : ℂ) : AnalyticAt ℂ riemannZeta₁ z :=
  DifferentiableOn.analyticAt differentiable_riemannZeta₁.differentiableOn Filter.univ_mem

/-- **`F` is analytic wherever `riemannZeta₁` does not vanish.** -/
lemma analyticAt_F {z : ℂ} (hz : riemannZeta₁ z ≠ 0) : AnalyticAt ℂ F z := by
  have hF : F = fun s ↦ -(deriv riemannZeta₁ s / riemannZeta₁ s) := by
    funext s; simp [F, logDeriv_apply]
  rw [hF]
  exact (((analyticAt_riemannZeta₁ z).deriv).div (analyticAt_riemannZeta₁ z) hz).neg

/-- **`F` is analytic at `s = 1`** — the property `A` lacks, and the reason `F` exists.

`riemannZeta₁ 1 = 1`, so no limit or removable-singularity argument is needed. -/
lemma analyticAt_F_one : AnalyticAt ℂ F 1 :=
  analyticAt_F (by rw [riemannZeta₁_one]; norm_num)

/-- **`F` is meromorphic on the whole plane**, one of `prop_5_2`'s hypotheses, restated for `F`.

`riemannZeta₁` is entire, so this is `MeromorphicOn.logDeriv` with nothing to exclude — easier
than the corresponding fact for `A`, which had to route around the pole of `ζ`. -/
lemma meromorphicOn_F : MeromorphicOn F Set.univ := by
  have h : MeromorphicOn riemannZeta₁ Set.univ :=
    fun w _ ↦ (analyticAt_riemannZeta₁ w).meromorphicAt
  intro z hz
  exact (h.logDeriv z hz).neg

/-- `riemannZeta₁` commutes with conjugation.

Away from `1` this is `riemannZeta_conj` transported along `riemannZeta₁ s = (s-1) ζ s`; at `s = 1`
it is `riemannZeta₁_one` and `conj 1 = 1`. The split is unavoidable, since `ConjSymm` is a claim
about *every* `s` and the transporting identity is only available off the pole. -/
lemma riemannZeta₁_conj (s : ℂ) :
    riemannZeta₁ (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta₁ s) := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp [riemannZeta₁_one]
  · have hs' : (starRingEnd ℂ s) ≠ 1 := by
      intro h
      exact hs (by simpa using congrArg (starRingEnd ℂ) h)
    have hmul : ∀ w : ℂ, w ≠ 1 → riemannZeta₁ w = (w - 1) * riemannZeta w := by
      intro w hw
      rw [riemannZeta_eq_riemannZeta₁_div hw]
      field_simp
    rw [hmul _ hs', hmul _ hs, riemannZeta_conj, map_mul, map_sub, map_one]

/-- The derivative of `riemannZeta₁` commutes with conjugation. -/
lemma deriv_riemannZeta₁_conj (s : ℂ) :
    deriv riemannZeta₁ (starRingEnd ℂ s) = starRingEnd ℂ (deriv riemannZeta₁ s) := by
  have hfun : riemannZeta₁ = fun z ↦ starRingEnd ℂ (riemannZeta₁ (starRingEnd ℂ z)) := by
    funext z
    rw [riemannZeta₁_conj]
    simp
  conv_lhs => rw [hfun]
  exact deriv_conj_conj' riemannZeta₁ s

/-- **`ConjSymm F`**, one of `prop_5_2`'s hypotheses — restated for `F` rather than for `A`.

This is the one of the three that needed something genuinely new, because the route through `A`
does not survive at `s = 1`, where `A` has its pole and `F` does not. Going through
`riemannZeta₁` avoids the issue entirely: it is entire, so there is no exceptional point. -/
lemma conjSymm_F : CH2.ConjSymm F := by
  intro s
  simp only [F, logDeriv_apply, map_neg, neg_inj]
  rw [deriv_riemannZeta₁_conj, riemannZeta₁_conj, map_div₀]

/-- `riemannZeta₁` does not vanish identically near any point.

The identity theorem again, and the seed is free: `riemannZeta₁_one` gives `riemannZeta₁ 1 = 1`.
Compare `meromorphicOrderAt_riemannZeta_ne_top`, which had to find a seed at `s = 2` and route
around the pole. -/
lemma meromorphicOrderAt_riemannZeta₁_ne_top (z : ℂ) :
    meromorphicOrderAt riemannZeta₁ z ≠ ⊤ := by
  have h1an : AnalyticAt ℂ riemannZeta₁ 1 := analyticAt_riemannZeta₁ 1
  have h1 : meromorphicOrderAt riemannZeta₁ 1 ≠ ⊤ := by
    rw [h1an.meromorphicOrderAt_eq,
      h1an.analyticOrderAt_eq_zero.mpr (by rw [riemannZeta₁_one]; norm_num)]
    simp
  have hmero : MeromorphicOn riemannZeta₁ Set.univ :=
    fun w _ ↦ (analyticAt_riemannZeta₁ w).meromorphicAt
  exact hmero.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ 1) (Set.mem_univ z) h1

/-- **`HasSimplePolesOn F Set.univ`**, the last of the three hypotheses restated for `F`.

Identical in shape to `hasSimplePolesOn_A_univ`, run on `riemannZeta₁` instead of on `ζ`. The
logarithmic derivative of a meromorphic function has order exactly `-1` at any zero or pole and
order `≥ 0` elsewhere, whatever the multiplicity — the multiplicity lands in the residue. -/
lemma hasSimplePolesOn_F_univ : HasSimplePolesOn F Set.univ := by
  intro z _
  have hζ : MeromorphicAt riemannZeta₁ z := (analyticAt_riemannZeta₁ z).meromorphicAt
  have hconst : meromorphicOrderAt (fun _ : ℂ ↦ (-1 : ℂ)) z = 0 := by
    rw [analyticAt_const.meromorphicOrderAt_eq, analyticAt_const.analyticOrderAt_eq_zero.mpr
      (by norm_num)]
    rfl
  have hFeq : F = (fun _ : ℂ ↦ (-1 : ℂ)) • logDeriv riemannZeta₁ := by funext w; simp [F]
  have hF : meromorphicOrderAt F z = meromorphicOrderAt (logDeriv riemannZeta₁) z := by
    rw [hFeq, meromorphicOrderAt_smul analyticAt_const.meromorphicAt hζ.logDeriv, hconst, zero_add]
  rw [hF]
  by_cases h0 : meromorphicOrderAt riemannZeta₁ z = 0
  · refine le_trans ?_ (meromorphicOrderAt_logDeriv_nonneg hζ h0)
    decide
  · rw [meromorphicOrderAt_logDeriv_eq_neg_one hζ h0 (meromorphicOrderAt_riemannZeta₁_ne_top z)]
    norm_cast

end CH2ZetaInstance
