/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section5
import IEANTN.Nodes.ZetaLogDeriv.v1.Conclusions
import IEANTN.Nodes.GammaAsymptotics.v2.Conclusions

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

/-- **A closed coordinate box in `ℂ` is compact.**

Every compact piece the ladder is cut into is a box, most of them degenerate: the columns have
`a = b`, the horizontal rays and the contour have `c = d`, and the `Re s = 1` segment has `a = b`
again. One lemma covers all of them, which is why this is stated in place of a fourth variant of
`isCompact_reOne_segment` — that one is kept because it is what `exists_ordinate_free_height`
already uses. -/
lemma isCompact_box (a b c d : ℝ) :
    IsCompact {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d} := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · have hEq : {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}
        = {z : ℂ | a ≤ z.re} ∩ ({z : ℂ | z.re ≤ b} ∩
            ({z : ℂ | c ≤ z.im} ∩ {z : ℂ | z.im ≤ d})) := by
      ext z; constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩
    rw [hEq]
    exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const)))
  · refine (Metric.isBounded_iff_subset_closedBall 0).mpr
      ⟨(|a| + |b|) + (|c| + |d|), fun z hz ↦ ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hz
    simp only [Metric.mem_closedBall, dist_zero_right]
    have hre : |z.re| ≤ |a| + |b| := by
      rcases le_or_gt 0 z.re with h | h
      · rw [abs_of_nonneg h]; linarith [le_abs_self b, abs_nonneg a]
      · rw [abs_of_neg h]; linarith [neg_abs_le a, abs_nonneg b]
    have him : |z.im| ≤ |c| + |d| := by
      rcases le_or_gt 0 z.im with h | h
      · rw [abs_of_nonneg h]; linarith [le_abs_self d, abs_nonneg c]
      · rw [abs_of_neg h]; linarith [neg_abs_le c, abs_nonneg d]
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ (|a| + |b|) + (|c| + |d|) := by linarith

/-- `IsBoundedNoPolesOn` restricts to a subset: both halves are pointwise. -/
lemma isBoundedNoPolesOn_mono {f : ℂ → ℂ} {S T : Set ℂ}
    (h : CH2.IsBoundedNoPolesOn f T) (hST : S ⊆ T) : CH2.IsBoundedNoPolesOn f S := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun z hz ↦ hM z (hST hz)⟩

/-- `IsBoundedNoPolesOn` on a union, by taking the larger bound.

The ladder is a union of seven pieces once split at `Re = -1`, so this is used repeatedly and is
worth having rather than unfolding the existential each time. -/
lemma isBoundedNoPolesOn_union {f : ℂ → ℂ} {S T : Set ℂ}
    (hS : CH2.IsBoundedNoPolesOn f S) (hT : CH2.IsBoundedNoPolesOn f T) :
    CH2.IsBoundedNoPolesOn f (S ∪ T) := by
  obtain ⟨M, hM⟩ := hS
  obtain ⟨N, hN⟩ := hT
  refine ⟨max M N, fun z hz ↦ ?_⟩
  rcases hz with h | h
  · exact ⟨(hM z h).1.trans (le_max_left _ _), (hM z h).2⟩
  · exact ⟨(hN z h).1.trans (le_max_right _ _), (hN z h).2⟩

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

/-! ### The leftward rays

The last shape in `l.Rboundary ∪ l.admissible_contour ∪ l.L` that the compact argument does not
reach: sets running off to `Re s = -∞` at bounded height. Every one of them is of that form — the
horizontal pieces `{Re s ≤ 1, Im s = ±T}` and `{Re s ≤ 1, Im s = δ}`, and the ladder `L`, whose
columns have `|Im s| ≤ T` and abscissas marching to `-∞`.

On these the `x₀ ^ s` factor is doing the work. `‖x₀ ^ s‖ = x₀ ^ Re s`, which decays exponentially
in `|Re s|` when `x₀ > 1`, and that beats any polynomial growth of `F`. Since the true growth of
`ζ'/ζ` out there is only logarithmic, stating the hypothesis with LINEAR growth costs nothing and
is much easier to supply — and it absorbs the extra factor of `s` in `prop_5_2`'s second
boundedness hypothesis, which then only changes the constant. -/

/-- `(a + b u) e^{-c u} ≤ a + b/c` for `u ≥ 0`.

The whole reason the rays are bounded, in one line of real analysis. The `u` term is beaten by
`c u ≤ exp (c u)`, which is `Real.add_one_le_exp`. -/
theorem linear_mul_exp_neg_le {a b c u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hu : 0 ≤ u) : (a + b * u) * Real.exp (-(c * u)) ≤ a + b / c := by
  have hcu : 0 ≤ c * u := mul_nonneg hc.le hu
  have hle_one : Real.exp (-(c * u)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hu_bound : u * Real.exp (-(c * u)) ≤ 1 / c := by
    rw [le_div_iff₀ hc]
    have h1 : c * u ≤ Real.exp (c * u) := by linarith [Real.add_one_le_exp (c * u)]
    have h2 : u * Real.exp (-(c * u)) * c = (c * u) * Real.exp (-(c * u)) := by ring
    rw [h2]
    calc (c * u) * Real.exp (-(c * u))
        ≤ Real.exp (c * u) * Real.exp (-(c * u)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  calc (a + b * u) * Real.exp (-(c * u))
      = a * Real.exp (-(c * u)) + b * (u * Real.exp (-(c * u))) := by ring
    _ ≤ a * 1 + b * (1 / c) := by gcongr
    _ = a + b / c := by ring

/-- `u² e^{-cu}` is bounded on `u ≥ 0`, and the bound comes free from the linear case.

The trick is `u² e^{-cu} = (u e^{-(c/2)u})²`: halving the rate turns the square of a product into
a product of squares, and the inner factor is the linear lemma at `c/2`. Doing it this way avoids
a second calculus argument. -/
theorem sq_mul_exp_neg_le {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    u ^ 2 * Real.exp (-(c * u)) ≤ (2 / c) ^ 2 := by
  have hlin : u * Real.exp (-(c / 2 * u)) ≤ 2 / c := by
    have h := linear_mul_exp_neg_le (a := 0) (b := 1) (c := c / 2) le_rfl zero_le_one
      (by linarith) hu
    simpa using h
  have hexp : Real.exp (-(c / 2 * u)) ^ 2 = Real.exp (-(c * u)) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hEq : u ^ 2 * Real.exp (-(c * u)) = (u * Real.exp (-(c / 2 * u))) ^ 2 := by
    rw [mul_pow, hexp]
  rw [hEq]
  exact pow_le_pow_left₀ (by positivity) hlin 2

/-- **Quadratic growth is also beaten by `x₀ ^ z` on `Re z ≤ 0`.**

The companion to `exists_bound_of_linear_growth_mul_cpow`, needed because `prop_5_2`'s *second*
boundedness hypothesis carries an extra factor of `zOf s = (s-1)/(iT)`, which turns the linear
growth of `F` into quadratic growth. The exponential still wins; this is the lemma that says so.

Expanding `(1 + u + C)²` gives a constant, a linear and a quadratic term, handled by
`linear_mul_exp_neg_le` and `sq_mul_exp_neg_le` respectively. -/
theorem exists_bound_of_quadratic_growth_mul_cpow {f : ℂ → ℂ} {S : Set ℂ} {x₀ C : ℝ}
    (hx₀ : 1 < x₀) (hC : 0 ≤ C) (hS : ∀ z ∈ S, z.re ≤ 0)
    (hbd : ∀ z ∈ S, ‖f z‖ ≤ C * (1 + ‖z‖) ^ 2) (hIm : ∀ z ∈ S, |z.im| ≤ C) :
    ∃ M, ∀ z ∈ S, ‖f z * (x₀ : ℂ) ^ z‖ ≤ M := by
  have hx₀pos : (0 : ℝ) < x₀ := by linarith
  have hlog : 0 < Real.log x₀ := Real.log_pos hx₀
  refine ⟨(C * (1 + C) ^ 2 + 2 * C * (1 + C) / Real.log x₀)
    + C * (2 / Real.log x₀) ^ 2, fun z hz ↦ ?_⟩
  have hre : z.re ≤ 0 := hS z hz
  set u : ℝ := -z.re with hu_def
  have hu : 0 ≤ u := by rw [hu_def]; linarith
  have habs : |z.re| = u := by rw [hu_def, abs_of_nonpos hre]
  have hnorm : ‖z‖ ≤ u + C := by
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    rw [habs]
    linarith [hIm z hz]
  -- `C (1 + ‖z‖)² ≤ C(1+C)² + 2C(1+C) u + C u²`.
  have hfz : ‖f z‖ ≤ C * (1 + C) ^ 2 + 2 * C * (1 + C) * u + C * u ^ 2 := by
    refine (hbd z hz).trans ?_
    have h1 : (1 : ℝ) + ‖z‖ ≤ 1 + C + u := by linarith
    have h0 : (0 : ℝ) ≤ 1 + ‖z‖ := by positivity
    have hsq : (1 + ‖z‖) ^ 2 ≤ (1 + C + u) ^ 2 := pow_le_pow_left₀ h0 h1 2
    calc C * (1 + ‖z‖) ^ 2 ≤ C * (1 + C + u) ^ 2 := mul_le_mul_of_nonneg_left hsq hC
      _ = C * (1 + C) ^ 2 + 2 * C * (1 + C) * u + C * u ^ 2 := by ring
  have hcpow : ‖(x₀ : ℂ) ^ z‖ = Real.exp (-(Real.log x₀ * u)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx₀pos, Real.rpow_def_of_pos hx₀pos]
    congr 1
    rw [hu_def]; ring
  rw [norm_mul, hcpow]
  have hexp_nonneg : (0 : ℝ) ≤ Real.exp (-(Real.log x₀ * u)) := (Real.exp_pos _).le
  calc ‖f z‖ * Real.exp (-(Real.log x₀ * u))
      ≤ (C * (1 + C) ^ 2 + 2 * C * (1 + C) * u + C * u ^ 2)
          * Real.exp (-(Real.log x₀ * u)) := mul_le_mul_of_nonneg_right hfz hexp_nonneg
    _ = (C * (1 + C) ^ 2 + 2 * C * (1 + C) * u) * Real.exp (-(Real.log x₀ * u))
          + C * (u ^ 2 * Real.exp (-(Real.log x₀ * u))) := by ring
    _ ≤ (C * (1 + C) ^ 2 + 2 * C * (1 + C) / Real.log x₀) + C * (2 / Real.log x₀) ^ 2 := by
        have h1 := linear_mul_exp_neg_le (a := C * (1 + C) ^ 2) (b := 2 * C * (1 + C))
          (c := Real.log x₀) (by positivity) (by positivity) hlog hu
        have h2 := sq_mul_exp_neg_le hlog hu
        have h3 : C * (u ^ 2 * Real.exp (-(Real.log x₀ * u))) ≤ C * (2 / Real.log x₀) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 hC
        linarith

/-- **A function of at most linear growth, damped by `x₀ ^ s` with `x₀ > 1`, is bounded on any set
in the closed left half-plane of bounded height.**

`x₀ > 1` is not a convenience. `prop_5_2`'s signature asks only `1 ≤ x₀`, but at `x₀ = 1` the
damping factor is identically `1` and the statement is false: `ζ'/ζ` is unbounded along the ladder,
whose columns march to `-∞`. -/
theorem exists_bound_of_linear_growth_mul_cpow {f : ℂ → ℂ} {S : Set ℂ} {x₀ C : ℝ}
    (hx₀ : 1 < x₀) (hC : 0 ≤ C) (hS : ∀ z ∈ S, z.re ≤ 0)
    (hbd : ∀ z ∈ S, ‖f z‖ ≤ C * (1 + ‖z‖)) (hIm : ∀ z ∈ S, |z.im| ≤ C) :
    ∃ M, ∀ z ∈ S, ‖f z * (x₀ : ℂ) ^ z‖ ≤ M := by
  have hx₀pos : (0 : ℝ) < x₀ := by linarith
  have hlog : 0 < Real.log x₀ := Real.log_pos hx₀
  refine ⟨C * (1 + C) + C / Real.log x₀, fun z hz ↦ ?_⟩
  have hre : z.re ≤ 0 := hS z hz
  set u : ℝ := -z.re with hu_def
  have hu : 0 ≤ u := by rw [hu_def]; linarith
  have habs : |z.re| = u := by rw [hu_def, abs_of_nonpos hre]
  have hnorm : ‖z‖ ≤ u + C := by
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    rw [habs]
    linarith [hIm z hz]
  have hfz : ‖f z‖ ≤ C * (1 + C) + C * u := by
    refine (hbd z hz).trans ?_
    have h1 : (1 : ℝ) + ‖z‖ ≤ (1 + C) + u := by linarith
    nlinarith
  have hcpow : ‖(x₀ : ℂ) ^ z‖ = Real.exp (-(Real.log x₀ * u)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx₀pos, Real.rpow_def_of_pos hx₀pos]
    congr 1
    rw [hu_def]; ring
  rw [norm_mul, hcpow]
  calc ‖f z‖ * Real.exp (-(Real.log x₀ * u))
      ≤ (C * (1 + C) + C * u) * Real.exp (-(Real.log x₀ * u)) :=
        mul_le_mul_of_nonneg_right hfz (Real.exp_pos _).le
    _ ≤ C * (1 + C) + C / Real.log x₀ :=
        linear_mul_exp_neg_le (by nlinarith) hC hlog hu

/-! ### A concrete ladder for `ζ`

Everything above is about pieces; this assembles them into an actual `LadderParams`. The three
free data are the abscissas, the height and the contour offset, and each is now pinned:
`σ n = 1 - 2n` from the trivial zeros being even, and `T`, `δ` from
`exists_ordinate_free_height`. -/

/-- Heights and offsets exist meeting every constraint `LadderParams` and the ladder impose.

`T` is drawn from `[20, 21]` and `δ` from `[1, 2]`, which forces `δ < T/4` since `T/4 ≥ 5`. The
numbers are arbitrary — any pair of intervals with the same separation would do — and they are
concrete only because that is cheaper than carrying the inequality abstractly. -/
theorem exists_ladder_heights :
    ∃ T δ : ℝ, 0 < T ∧ 0 < δ ∧ δ < T / 4 ∧
      (∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ T) ∧
      (∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ δ) := by
  obtain ⟨T, hT1, hT2, hTfree⟩ := exists_ordinate_free_height (T₀ := 20) (by norm_num)
  obtain ⟨δ, hd1, hd2, hdfree⟩ := exists_ordinate_free_height (T₀ := 1) (by norm_num)
  exact ⟨T, δ, by linarith, by linarith, by linarith, hTfree, hdfree⟩

/-- **A `LadderParams` whose ladder and contour miss every zero of `ζ`.**

This is the object `prop_5_2` is to be applied with. The abscissas are `sigmaZeta`, so the columns
thread between the trivial zeros; the height and offset come from `exists_ladder_heights`, so the
horizontal pieces miss the non-trivial ones.

Stated as an existence rather than a `def` on purpose: nothing downstream should depend on *which*
admissible `T` and `δ` were chosen, only that some choice works. -/
theorem exists_ladderParams_zeta :
    ∃ l : CH2.LadderParams, l.σ = sigmaZeta ∧
      (∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T) ∧
      (∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.δ) := by
  obtain ⟨T, δ, hT, hd0, hdT, hTfree, hdfree⟩ := exists_ladder_heights
  refine ⟨{ σ := sigmaZeta, T := T, δ := δ, h0 := ?_, hσ := ?_, hlim := ?_, hδ := ?_ },
    rfl, hTfree, hdfree⟩
  · simp [sigmaZeta]
  · intro n
    simp only [sigmaZeta]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · -- `1 - 2n -> -infinity`. Mathlib has no `const_sub` lemma landing in `atBot`, so this is the
    -- direct argument: past `ceil ((1-b)/2)` the value is below `b`.
    refine Filter.tendsto_atBot.2 (fun b ↦ ?_)
    filter_upwards [Filter.eventually_ge_atTop (Nat.ceil ((1 - b) / 2))] with n hn
    have h : ((1 - b) / 2 : ℝ) ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    simp only [sigmaZeta]
    linarith
  · exact ⟨hd0, hdT⟩

/-! ### `tan` is bounded off the real axis

The last input the growth bound needs, and Mathlib has nothing like it: its only results about
`Complex.tan` say it blows up AT the poles (`tendsto_norm_tan_of_cos_eq_zero`), not that it stays
bounded away from them. A contour argument needs the second.

The identity `‖cos w‖² = cos²(Re w) + sinh²(Im w)` is what makes it easy, and it follows from
`Complex.cos_add_mul_I` plus `Real.cosh_sq`. Both it and the `sin` analogue look like Mathlib
lemmas in their own right. -/


/-- `‖cos w‖² = cos²(Re w) + sinh²(Im w)`. -/
theorem norm_cos_sq (w : ℂ) :
    ‖Complex.cos w‖ ^ 2 = Real.cos w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have h := Complex.cos_add_mul_I (w.re : ℂ) (w.im : ℂ)
  rw [Complex.re_add_im] at h
  rw [h, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hc := Real.cosh_sq w.im
  have hs := Real.sin_sq_add_cos_sq w.re
  nlinarith [hc, hs, sq_nonneg (Real.cos w.re), sq_nonneg (Real.sinh w.im)]

/-- `‖sin w‖² = sin²(Re w) + sinh²(Im w)`. -/
theorem norm_sin_sq (w : ℂ) :
    ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have h := Complex.sin_add_mul_I (w.re : ℂ) (w.im : ℂ)
  rw [Complex.re_add_im] at h
  rw [h, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hc := Real.cosh_sq w.im
  have hs := Real.sin_sq_add_cos_sq w.re
  nlinarith [hc, hs, sq_nonneg (Real.sin w.re), sq_nonneg (Real.sinh w.im)]

/-- **`‖tan w‖ ≤ cosh(Im w) / |sinh(Im w)|`** — `tan` is bounded off the real axis.

Mathlib has no upper bound on `‖Complex.tan‖` at all, only that it blows up at the poles. This is
what a contour argument needs: along a horizontal line at fixed non-zero height, `tan` is bounded,
and the bound depends only on the height. -/
theorem norm_tan_le_of_im_ne_zero {w : ℂ} (h : w.im ≠ 0) :
    ‖Complex.tan w‖ ≤ Real.cosh w.im / |Real.sinh w.im| := by
  have hsinh : Real.sinh w.im ≠ 0 := fun hc ↦ h (by simpa using Real.sinh_eq_zero.mp hc)
  have habs : 0 < |Real.sinh w.im| := abs_pos.mpr hsinh
  have hcos : ‖Complex.cos w‖ ≠ 0 := by
    intro hc
    have := norm_cos_sq w
    rw [hc] at this
    nlinarith [sq_nonneg (Real.cos w.re), sq_abs (Real.sinh w.im), habs]
  rw [Complex.tan_eq_sin_div_cos, norm_div, div_le_div_iff₀ (by positivity) habs]
  have h1 : ‖Complex.sin w‖ ^ 2 ≤ Real.cosh w.im ^ 2 := by
    rw [norm_sin_sq]
    nlinarith [Real.sin_sq_add_cos_sq w.re, Real.cosh_sq w.im, sq_nonneg (Real.cos w.re)]
  have h2 : |Real.sinh w.im| ^ 2 ≤ ‖Complex.cos w‖ ^ 2 := by
    rw [norm_cos_sq, sq_abs]
    nlinarith [sq_nonneg (Real.cos w.re)]
  have hsin_nn : (0:ℝ) ≤ ‖Complex.sin w‖ := norm_nonneg _
  have hcosh_pos : 0 < Real.cosh w.im := Real.cosh_pos _
  have hcos_nn : (0:ℝ) ≤ ‖Complex.cos w‖ := norm_nonneg _
  -- Take square roots of `h1` and `h2`, then multiply.
  have hsin_le : ‖Complex.sin w‖ ≤ Real.cosh w.im := by
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hsin_nn, Real.sqrt_sq hcosh_pos.le] at this
  have hsinh_le : |Real.sinh w.im| ≤ ‖Complex.cos w‖ := by
    have := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq hcos_nn] at this
  exact mul_le_mul hsin_le hsinh_le (abs_nonneg _) hcosh_pos.le

/-- **`‖tan w‖ ≤ 1` when `Re w` is a multiple of `π`.**

The companion to `norm_tan_le_of_im_ne_zero`, and the one the ladder COLUMNS need. That lemma's
bound is `cosh(Im w)/|sinh(Im w)|`, which diverges as `Im w → 0`, and a column carries
`|Im z| ≤ T` *including zero*, so it does not reach there at all. The gap was not noticed until
the two boundedness hypotheses of `prop_5_2` were assembled, because until then nothing asked for
a `tan` bound on a set meeting the real axis.

Along a column the estimate is easier rather than harder. `sin (Re w) = 0` forces
`cos²(Re w) = 1`, so `‖sin w‖² = sinh²(Im w)` and `‖cos w‖² = 1 + sinh²(Im w) = cosh²(Im w)`, and
the quotient is `|tanh (Im w)| ≤ 1` — a bound with no dependence on the height at all. -/
theorem norm_tan_le_one_of_sin_re_eq_zero {w : ℂ} (h : Real.sin w.re = 0) :
    ‖Complex.tan w‖ ≤ 1 := by
  have hcos_sq : Real.cos w.re ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq w.re
    nlinarith [h]
  have hs : ‖Complex.sin w‖ ^ 2 = Real.sinh w.im ^ 2 := by
    rw [norm_sin_sq, h]; ring
  have hc : ‖Complex.cos w‖ ^ 2 = 1 + Real.sinh w.im ^ 2 := by
    rw [norm_cos_sq, hcos_sq]
  have hcpos : 0 < ‖Complex.cos w‖ := by
    have hsq : (0 : ℝ) < ‖Complex.cos w‖ ^ 2 := by rw [hc]; positivity
    nlinarith [norm_nonneg (Complex.cos w)]
  rw [Complex.tan_eq_sin_div_cos, norm_div, div_le_one hcpos]
  nlinarith [norm_nonneg (Complex.sin w), norm_nonneg (Complex.cos w), hs, hc]

/-- **On a ladder column the tangent factor is bounded by `1`**, uniformly in the column and in
the height.

The column `Re z = 1 - 2n` makes the argument `π(1-z)/2` have real part exactly `π n`, which is
where `norm_tan_le_one_of_sin_re_eq_zero` applies. The parity is doing the work again, as it does
in `cos_ne_zero_on_column`: an odd abscissa would put the real part at a half-integer multiple of
`π`, where `cos` vanishes and `tan` has its poles. -/
theorem norm_tan_le_one_on_column {n : ℕ} {z : ℂ} (hz : z.re = sigmaZeta n) :
    ‖Complex.tan ((Real.pi : ℂ) * (1 - z) / 2)‖ ≤ 1 := by
  refine norm_tan_le_one_of_sin_re_eq_zero ?_
  have hEq : (Real.pi : ℂ) * (1 - z) / 2 = ((Real.pi / 2 : ℝ) : ℂ) * (1 - z) := by
    push_cast; ring
  have hre : ((Real.pi : ℂ) * (1 - z) / 2).re = (n : ℝ) * Real.pi := by
    rw [hEq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, hz, sigmaZeta]
    ring
  rw [hre]
  exact Real.sin_nat_mul_pi n

/-! ### Cutting the ladder at `Re = -1`

`prop_5_2`'s two boundedness hypotheses are about
`l.Rboundary ∪ l.admissible_contour ∪ l.L`, a set that is neither compact nor contained in the
region where the growth bound applies. It has to be cut, and `Re z = -1` is where: to the right
the set is compact, so `isBoundedNoPolesOn_of_isCompact` settles it; to the left `norm_F_le_linear`
applies, since it wants `Re z ≤ -1`.

The cut is clean because the ladder's first column sits exactly at `Re = -1` (`σ 1 = -1`), so no
column is split by it — every other column has `Re = 1 - 2n ≤ -3`. -/

/-- The part of the ladder with `Re z ≥ -1`, written as a union of five boxes.

In order: the `Re = 1` segment of `∂R`, the near parts of the two horizontal rays at `|Im| = T`,
the near part of the contour ray at `Im = δ`, and the first ladder column at `Re = -1`. Four of
the five are degenerate — a segment rather than a rectangle — which is why `isCompact_box` is
stated with independent bounds on each coordinate. -/
def nearLadder (T δ : ℝ) : Set ℂ :=
  {z : ℂ | 1 ≤ z.re ∧ z.re ≤ 1 ∧ -T ≤ z.im ∧ z.im ≤ T} ∪
    ({z : ℂ | -1 ≤ z.re ∧ z.re ≤ 1 ∧ T ≤ z.im ∧ z.im ≤ T} ∪
      ({z : ℂ | -1 ≤ z.re ∧ z.re ≤ 1 ∧ -T ≤ z.im ∧ z.im ≤ -T} ∪
        ({z : ℂ | -1 ≤ z.re ∧ z.re ≤ 1 ∧ δ ≤ z.im ∧ z.im ≤ δ} ∪
          {z : ℂ | -1 ≤ z.re ∧ z.re ≤ -1 ∧ -T ≤ z.im ∧ z.im ≤ T})))

lemma isCompact_nearLadder (T δ : ℝ) : IsCompact (nearLadder T δ) :=
  (isCompact_box 1 1 (-T) T).union ((isCompact_box (-1) 1 T T).union
    ((isCompact_box (-1) 1 (-T) (-T)).union ((isCompact_box (-1) 1 δ δ).union
      (isCompact_box (-1) (-1) (-T) T))))

/-- **The cut is a cover**: everything on the ladder with `Re z ≥ -1` lies in one of the boxes.

The only case with any content is `l.L`: a column has `Re = 1 - 2n` with `n ≥ 1`, and
`1 - 2n ≥ -1` forces `n ≤ 1`, hence `n = 1` and `Re = -1` exactly. Every other column is at
`Re ≤ -3` and falls on the other side of the cut. -/
theorem nearLadder_covers {l : CH2.LadderParams} (hσ : l.σ = sigmaZeta) :
    (l.Rboundary ∪ l.admissible_contour ∪ l.L) ∩ {z : ℂ | -1 ≤ z.re}
      ⊆ nearLadder l.T l.δ := by
  have hT : 0 < l.T := l.hT
  have hδ0 : 0 < l.δ := l.hδ.1
  have hδT : l.δ < l.T / 4 := l.hδ.2
  rintro z ⟨hz, hre⟩
  simp only [Set.mem_setOf_eq] at hre
  simp only [nearLadder, Set.mem_union, Set.mem_setOf_eq]
  rcases hz with (hb | hc) | hl
  · -- `∂R`: the `Re = 1` segment, or a horizontal ray at `|Im| = T`.
    simp only [CH2.LadderParams.Rboundary, Set.mem_setOf_eq] at hb
    rcases hb with ⟨hre1, him⟩ | ⟨hre1, him⟩
    · exact Or.inl ⟨hre1.ge, hre1.le, (abs_le.mp him).1, (abs_le.mp him).2⟩
    · rcases abs_eq (le_of_lt hT) |>.mp him with h | h
      · exact Or.inr (Or.inl ⟨hre, hre1, h.ge, h.le⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hre, hre1, h.ge, h.le⟩))
  · -- The contour: the ray at `Im = δ`, or the short segment on `Re = 1`.
    simp only [CH2.LadderParams.admissible_contour, Set.mem_setOf_eq] at hc
    rcases hc with ⟨hre1, him⟩ | ⟨hre1, him⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hre, hre1, him.ge, him.le⟩)))
    · refine Or.inl ⟨hre1.ge, hre1.le, ?_, ?_⟩
      · linarith [him.1]
      · linarith [him.2]
  · -- A column, and only the first one survives the cut.
    simp only [CH2.LadderParams.L, Set.mem_setOf_eq] at hl
    obtain ⟨n, hn, hrn, him⟩ := hl
    rw [hσ] at hrn
    have hn1 : n = 1 := by
      by_contra hne
      have h2 : 2 ≤ n := lt_of_le_of_ne hn (Ne.symm hne)
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
      rw [hrn] at hre
      simp only [sigmaZeta] at hre
      linarith
    rw [hn1] at hrn
    simp only [sigmaZeta, Nat.cast_one] at hrn
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, (abs_le.mp him).1, (abs_le.mp him).2⟩)))
    · rw [hrn]; norm_num
    · rw [hrn]; norm_num

/-- `F` is analytic wherever `ζ` does not vanish, away from `s = 1`.

The detour through `ζ₁` is what makes `s = 1` a separate case: `ζ` has a pole there, so the
zero-transfer lemma excludes it, and `analyticAt_F_one` covers it instead. -/
lemma analyticAt_F_of_zeta_ne_zero {z : ℂ} (hz1 : z ≠ 1) (h : riemannZeta z ≠ 0) :
    AnalyticAt ℂ F z :=
  analyticAt_F (fun hc ↦ h ((riemannZeta_eq_zero_iff_riemannZeta₁ hz1).mpr hc))

/-- **`F` is analytic on the whole near part of the ladder**, which is the second half of
`IsBoundedNoPolesOn` there and the reason the ladder's parameters were chosen as they were.

One box at a time: `Re = 1` is Mathlib's non-vanishing on the closed half-plane, with `s = 1`
peeled off; the three degenerate boxes at `|Im| = T` and `Im = δ` are exactly what
`exists_ordinate_free_height` bought; and the last is the first column, where the parity argument
of `riemannZeta_ne_zero_on_column` applies.

Note this does NOT need `l.σ = sigmaZeta`, unlike `nearLadder_covers`: the abscissa choice is
already baked into the boxes, and what is used here is only that `sigmaZeta 1 = -1`. -/
theorem analyticAt_F_of_mem_nearLadder {l : CH2.LadderParams}
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T)
    (hδfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.δ)
    {z : ℂ} (hz : z ∈ nearLadder l.T l.δ) : AnalyticAt ℂ F z := by
  have hT : 0 < l.T := l.hT
  have hδ0 : 0 < l.δ := l.hδ.1
  simp only [nearLadder, Set.mem_union, Set.mem_setOf_eq] at hz
  rcases hz with ⟨h1, _, _, _⟩ | ⟨_, _, h3, h4⟩ | ⟨_, _, h3, h4⟩ | ⟨_, _, h3, h4⟩ | ⟨h1, h2, _, _⟩
  · rcases eq_or_ne z 1 with rfl | hz1
    · exact analyticAt_F_one
    · exact analyticAt_F_of_zeta_ne_zero hz1 (riemannZeta_ne_zero_of_one_le_re h1)
  · have him : z.im = l.T := le_antisymm h4 h3
    have hz1 : z ≠ 1 := by
      intro h; rw [h] at him; simp only [Complex.one_im] at him; linarith
    exact analyticAt_F_of_zeta_ne_zero hz1
      (fun hc ↦ hTfree z hc (by rw [him, abs_of_pos hT]))
  · have him : z.im = -l.T := le_antisymm h4 h3
    have hz1 : z ≠ 1 := by
      intro h; rw [h] at him; simp only [Complex.one_im] at him; linarith
    exact analyticAt_F_of_zeta_ne_zero hz1
      (fun hc ↦ hTfree z hc (by rw [him, abs_neg, abs_of_pos hT]))
  · have him : z.im = l.δ := le_antisymm h4 h3
    have hz1 : z ≠ 1 := by
      intro h; rw [h] at him; simp only [Complex.one_im] at him; linarith
    exact analyticAt_F_of_zeta_ne_zero hz1
      (fun hc ↦ hδfree z hc (by rw [him, abs_of_pos hδ0]))
  · have hre : z.re = sigmaZeta 1 := by
      have : z.re = -1 := le_antisymm h2 h1
      rw [this]; norm_num [sigmaZeta]
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hre
      simp only [Complex.one_re, sigmaZeta] at hre
      norm_num at hre
    exact analyticAt_F_of_zeta_ne_zero hz1 (riemannZeta_ne_zero_on_column le_rfl hre)

/-- `x₀ ^ s` is entire in `s` for a positive real base. -/
lemma analyticAt_const_cpow {x₀ : ℝ} (hx₀ : 0 < x₀) (z : ℂ) :
    AnalyticAt ℂ (fun s : ℂ ↦ (x₀ : ℂ) ^ s) z :=
  (Differentiable.const_cpow differentiable_id
    (Or.inl (Complex.ofReal_ne_zero.mpr hx₀.ne'))).analyticAt z

/-- `zOf` is entire: it is `(s - 1)` divided by a constant. -/
lemma analyticAt_zOf (l : CH2.LadderParams) (z : ℂ) : AnalyticAt ℂ l.zOf z := by
  have hd : Differentiable ℂ (fun s : ℂ ↦ (s - 1) / (Complex.I * l.T)) :=
    (differentiable_id.sub_const 1).div_const _
  exact hd.analyticAt z

/-- **The near half of `prop_5_2`'s first boundedness hypothesis.** -/
theorem isBoundedNoPolesOn_nearLadder {l : CH2.LadderParams}
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T)
    (hδfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.δ)
    {x₀ : ℝ} (hx₀ : 0 < x₀) :
    CH2.IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) (nearLadder l.T l.δ) :=
  isBoundedNoPolesOn_of_isCompact (isCompact_nearLadder _ _)
    (fun z hz ↦ (analyticAt_F_of_mem_nearLadder hTfree hδfree hz).mul
      (analyticAt_const_cpow hx₀ z))

/-- **The near half of `prop_5_2`'s second boundedness hypothesis**, with the extra `zOf` factor.

The factor is entire, so it changes nothing on a compact set — which is the point of stating
`isBoundedNoPolesOn_of_isCompact` for a general `f` rather than for `F`. -/
theorem isBoundedNoPolesOn_nearLadder_weighted {l : CH2.LadderParams}
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T)
    (hδfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.δ)
    {x₀ : ℝ} (hx₀ : 0 < x₀) :
    CH2.IsBoundedNoPolesOn (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s) (nearLadder l.T l.δ) :=
  isBoundedNoPolesOn_of_isCompact (isCompact_nearLadder _ _)
    (fun z hz ↦ ((analyticAt_zOf l z).mul
      (analyticAt_F_of_mem_nearLadder hTfree hδfree hz)).mul (analyticAt_const_cpow hx₀ z))

/-! ### The far part of the ladder, `Re z ≤ -1`

Here the set is unbounded and compactness is no help; what applies instead is `norm_F_le_linear`,
whose two side conditions are that the cosine does not vanish and the tangent is bounded. Both
split the same way, and the split is the reason `norm_tan_le_one_of_sin_re_eq_zero` had to exist:

* on the two horizontal rays and the contour ray, `Im z` is pinned to `±T` or `δ`, all non-zero,
  so `norm_tan_le_of_im_ne_zero` applies and the bound depends on the height;
* on the columns, `Im z` ranges over `[-T, T]` and passes through zero, where that bound is
  infinite — but the column's abscissa puts the argument's real part at a multiple of `π`, and the
  bound is `1`. -/

/-- `cos w ≠ 0` off the real axis: `‖cos w‖² = cos²(Re w) + sinh²(Im w)` and the second term is
positive. -/
lemma cos_ne_zero_of_im_ne_zero {w : ℂ} (h : w.im ≠ 0) : Complex.cos w ≠ 0 := by
  intro hc
  have hnorm := norm_cos_sq w
  rw [hc] at hnorm
  have hs : Real.sinh w.im ≠ 0 := fun hz ↦ h (by simpa using Real.sinh_eq_zero.mp hz)
  have hpos : 0 < Real.sinh w.im ^ 2 := by positivity
  simp only [norm_zero] at hnorm
  nlinarith [sq_nonneg (Real.cos w.re)]

/-- The bound `norm_tan_le_of_im_ne_zero` supplies, as a function of the height. -/
noncomputable def tanBound (y : ℝ) : ℝ := Real.cosh y / |Real.sinh y|

lemma tanBound_nonneg (y : ℝ) : 0 ≤ tanBound y :=
  div_nonneg (Real.cosh_pos y).le (abs_nonneg _)

lemma tanBound_neg (y : ℝ) : tanBound (-y) = tanBound y := by
  simp [tanBound, Real.cosh_neg, Real.sinh_neg, abs_neg]

/-- The imaginary part of the argument the functional equation puts the tangent at. -/
lemma im_pi_one_sub_div_two (z : ℂ) :
    ((Real.pi : ℂ) * (1 - z) / 2).im = -(Real.pi / 2 * z.im) := by
  have hEq : (Real.pi : ℂ) * (1 - z) / 2 = ((Real.pi / 2 : ℝ) : ℂ) * (1 - z) := by
    push_cast; ring
  rw [hEq]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
    Complex.one_im, Complex.sub_re, Complex.one_re]
  ring

/-- Membership in the far part forces `z` onto a ray at fixed non-zero height, or onto a column. -/
theorem farLadder_cases {l : CH2.LadderParams} (hσ : l.σ = sigmaZeta) {z : ℂ}
    (hz : z ∈ l.Rboundary ∪ l.admissible_contour ∪ l.L) (hre : z.re ≤ -1) :
    (z.im = l.T ∨ z.im = -l.T ∨ z.im = l.δ) ∨ ∃ n : ℕ, 1 ≤ n ∧ z.re = sigmaZeta n := by
  have hT : 0 < l.T := l.hT
  rcases hz with (hb | hc) | hl
  · simp only [CH2.LadderParams.Rboundary, Set.mem_setOf_eq] at hb
    rcases hb with ⟨hre1, _⟩ | ⟨_, him⟩
    · exfalso; rw [hre1] at hre; linarith
    · rcases abs_eq hT.le |>.mp him with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
  · simp only [CH2.LadderParams.admissible_contour, Set.mem_setOf_eq] at hc
    rcases hc with ⟨_, him⟩ | ⟨hre1, _⟩
    · exact Or.inl (Or.inr (Or.inr him))
    · exfalso; rw [hre1] at hre; linarith
  · simp only [CH2.LadderParams.L, Set.mem_setOf_eq] at hl
    obtain ⟨n, hn, hrn, _⟩ := hl
    rw [hσ] at hrn
    exact Or.inr ⟨n, hn, hrn⟩

/-- **The cosine does not vanish on the far part.** -/
theorem cos_ne_zero_on_farLadder {l : CH2.LadderParams} (hσ : l.σ = sigmaZeta) {z : ℂ}
    (hz : z ∈ l.Rboundary ∪ l.admissible_contour ∪ l.L) (hre : z.re ≤ -1) :
    Complex.cos ((Real.pi : ℂ) * (1 - z) / 2) ≠ 0 := by
  have hT : 0 < l.T := l.hT
  have hδ0 : 0 < l.δ := l.hδ.1
  have hpi := Real.pi_pos
  rcases farLadder_cases hσ hz hre with (him | him | him) | ⟨n, hn, hrn⟩
  · refine cos_ne_zero_of_im_ne_zero ?_
    rw [im_pi_one_sub_div_two, him]; intro h; nlinarith [h]
  · refine cos_ne_zero_of_im_ne_zero ?_
    rw [im_pi_one_sub_div_two, him]; intro h; nlinarith [h]
  · refine cos_ne_zero_of_im_ne_zero ?_
    rw [im_pi_one_sub_div_two, him]; intro h; nlinarith [h]
  · exact cos_ne_zero_on_column hrn

/-- **The tangent is bounded on the far part**, by a constant depending only on the ladder.

Existential rather than explicit: `norm_F_le_linear` consumes a bound and does not care which, and
naming `max (coth (πT/2)) (max (coth (πδ/2)) 1)` in the statement would commit to an ordering of
the three that would then have to be proved. -/
theorem exists_tan_bound_on_farLadder (l : CH2.LadderParams) (hσ : l.σ = sigmaZeta) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ l.Rboundary ∪ l.admissible_contour ∪ l.L, z.re ≤ -1 →
      ‖Complex.tan ((Real.pi : ℂ) * (1 - z) / 2)‖ ≤ B := by
  have hT : 0 < l.T := l.hT
  have hδ0 : 0 < l.δ := l.hδ.1
  have hpi := Real.pi_pos
  refine ⟨max (tanBound (Real.pi / 2 * l.T)) (max (tanBound (Real.pi / 2 * l.δ)) 1),
    le_trans (tanBound_nonneg _) (le_max_left _ _), fun z hz hre ↦ ?_⟩
  have hray : ∀ y : ℝ, y ≠ 0 → ((Real.pi : ℂ) * (1 - z) / 2).im = -(Real.pi / 2 * y) →
      ‖Complex.tan ((Real.pi : ℂ) * (1 - z) / 2)‖ ≤ tanBound (Real.pi / 2 * y) := by
    intro y hy him
    have hne : ((Real.pi : ℂ) * (1 - z) / 2).im ≠ 0 := by
      rw [him]
      intro h
      have : Real.pi / 2 * y = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact hy h'
    have hb := norm_tan_le_of_im_ne_zero hne
    rwa [him, show Real.cosh (-(Real.pi / 2 * y)) / |Real.sinh (-(Real.pi / 2 * y))|
      = tanBound (Real.pi / 2 * y) from by
        rw [← tanBound_neg (Real.pi / 2 * y)]; rfl] at hb
  rcases farLadder_cases hσ hz hre with (him | him | him) | ⟨n, hn, hrn⟩
  · exact le_trans (hray l.T hT.ne' (by rw [im_pi_one_sub_div_two, him])) (le_max_left _ _)
  · refine le_trans (hray (-l.T) (by simpa using hT.ne') ?_) ?_
    · rw [im_pi_one_sub_div_two, him]
    · rw [show Real.pi / 2 * -l.T = -(Real.pi / 2 * l.T) from by ring, tanBound_neg]
      exact le_max_left _ _
  · exact le_trans (hray l.δ hδ0.ne' (by rw [im_pi_one_sub_div_two, him]))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  · exact le_trans (norm_tan_le_one_on_column hrn)
      (le_trans (le_max_right _ _) (le_max_right _ _))

/-- The whole ladder lies within height `T`. Immediate from the definitions, but it is what pays
for `GammaAsymptotics.v2` being the strip version rather than the half-plane one. -/
theorem abs_im_le_T_of_mem_ladder {l : CH2.LadderParams} {z : ℂ}
    (hz : z ∈ l.Rboundary ∪ l.admissible_contour ∪ l.L) : |z.im| ≤ l.T := by
  have hT : 0 < l.T := l.hT
  have hδ0 : 0 < l.δ := l.hδ.1
  have hδT : l.δ < l.T / 4 := l.hδ.2
  rcases hz with (hb | hc) | hl
  · simp only [CH2.LadderParams.Rboundary, Set.mem_setOf_eq] at hb
    rcases hb with ⟨_, him⟩ | ⟨_, him⟩
    · exact him
    · exact him.le
  · simp only [CH2.LadderParams.admissible_contour, Set.mem_setOf_eq] at hc
    rcases hc with ⟨_, him⟩ | ⟨_, him⟩
    · rw [him, abs_of_pos hδ0]; linarith
    · rw [abs_le]; constructor <;> [linarith [him.1]; linarith [him.2]]
  · simp only [CH2.LadderParams.L, Set.mem_setOf_eq] at hl
    obtain ⟨_, _, _, him⟩ := hl
    exact him

lemma meromorphicOrderAt_nonneg_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ f z) :
    0 ≤ meromorphicOrderAt f z := by
  rw [h.meromorphicOrderAt_eq]
  exact ENat.map_natCast_nonneg

/-- **`F` is analytic on the far part**, for the same reasons as on the near part but read off
`farLadder_cases` instead of the boxes. -/
theorem analyticAt_F_of_mem_farLadder {l : CH2.LadderParams} (hσ : l.σ = sigmaZeta)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T)
    (hδfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.δ)
    {z : ℂ} (hz : z ∈ l.Rboundary ∪ l.admissible_contour ∪ l.L) (hre : z.re ≤ -1) :
    AnalyticAt ℂ F z := by
  have hT : 0 < l.T := l.hT
  have hδ0 : 0 < l.δ := l.hδ.1
  have hz1 : z ≠ 1 := by
    intro h; rw [h] at hre; simp only [Complex.one_re] at hre; linarith
  rcases farLadder_cases hσ hz hre with (him | him | him) | ⟨n, hn, hrn⟩
  · exact analyticAt_F_of_zeta_ne_zero hz1 (fun hc ↦ hTfree z hc (by rw [him, abs_of_pos hT]))
  · exact analyticAt_F_of_zeta_ne_zero hz1
      (fun hc ↦ hTfree z hc (by rw [him, abs_neg, abs_of_pos hT]))
  · exact analyticAt_F_of_zeta_ne_zero hz1 (fun hc ↦ hδfree z hc (by rw [him, abs_of_pos hδ0]))
  · exact analyticAt_F_of_zeta_ne_zero hz1 (riemannZeta_ne_zero_on_column hn hrn)

/-! ### The growth bound on `F`

The last estimate. Everything it consumes is now proved: the ladder-form identity, boundedness of
`ζ'/ζ` on `Re w ≥ 2`, the `tan` bound, and `GammaAsymptotics.v1`'s digamma estimate, which arrives
as a hypothesis rather than a `sorry` because `CH2.v1` imports that node.

The digamma input is `GammaAsymptotics.v2`, the STRIP version, and `hH` is what pays for it:
every piece of the ladder has `|Im s|` bounded by `T`, so the height restriction costs this
consumer nothing. See that node for why the half-plane version is harder and still open. -/

/-- `‖log w‖ ≤ ‖w‖ + π` once `‖w‖ ≥ 1`. Crude on purpose: only linear growth is needed. -/
theorem norm_log_le_norm_add_pi {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖Complex.log w‖ ≤ ‖w‖ + Real.pi := by
  have hlog_nn : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hw
  have hlog_le : Real.log ‖w‖ ≤ ‖w‖ := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < ‖w‖ by linarith)
    linarith
  calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖w‖| + |Complex.arg w| := by rw [Complex.log_re, Complex.log_im]
    _ ≤ ‖w‖ + Real.pi := by
        rw [abs_of_nonneg hlog_nn]
        have := Complex.abs_arg_le_pi w
        linarith

/-- `ζ₁ w = (w - 1) * ζ w` away from the pole. -/
theorem riemannZeta₁_eq_mul {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [riemannZeta_eq_inv_sub_add hs, riemannZeta₁]
  field_simp

/-- **The two descriptions of `F` agree**: `-logDeriv ζ₁ = -logDeriv ζ - 1/(s-1)`.

`F` is *defined* through `riemannZeta₁` because that is manifestly analytic at `s = 1`. This says
it really is Theorem 1.1's `A - Res_{s=1} A / (s-1)`, which is what the paper applies. -/
theorem logDeriv_riemannZeta₁_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta₁ s = logDeriv riemannZeta s + (s - 1)⁻¹ := by
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hEq : riemannZeta₁ =ᶠ[nhds s] (fun z ↦ (z - 1) * riemannZeta z) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show s ∈ ({(1 : ℂ)}ᶜ) from hs)] with z hz'
    exact riemannZeta₁_eq_mul hz'
  have h := (logDeriv_congr_nhds hEq).eq_of_nhds
  have hsub : logDeriv (fun z : ℂ ↦ z - 1) s = (s - 1)⁻¹ := by
    rw [logDeriv_apply]
    have hd : deriv (fun z : ℂ ↦ z - 1) s = 1 := by
      simpa using ((hasDerivAt_id s).sub_const (1 : ℂ)).deriv
    rw [hd, one_div]
  rw [h, logDeriv_fun_mul s hne hz (by fun_prop) (differentiableAt_riemannZeta hs), hsub]
  ring

/-- **`F` grows at most linearly on any set in `Re s ≤ -1` where `tan` is bounded.**

The hypotheses are exactly the two things that vary between the pieces of the target set: how big
`tan(π(1-s)/2)` gets, and that it is defined at all. Both are supplied per-piece — bounded by `1`
on a column by parity, and by `norm_tan_le_of_im_ne_zero` on a ray.

`hcos` is doing double duty. It keeps `tan` finite, and it also gives `ζ z ≠ 0` for free: its
failures are exactly the even integers, which include every trivial zero, so with `Re z ≤ -1` the
remaining points are covered by `riemannZeta_ne_zero_of_re_neg`. -/
theorem norm_F_le_linear
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    {S : Set ℂ} {B H : ℝ} (hB : 0 ≤ B)
    (hS : ∀ z ∈ S, z.re ≤ -1) (hH : ∀ z ∈ S, |z.im| ≤ H)
    (hcos : ∀ z ∈ S, Complex.cos ((Real.pi : ℂ) * (1 - z) / 2) ≠ 0)
    (htan : ∀ z ∈ S, ‖Complex.tan ((Real.pi : ℂ) * (1 - z) / 2)‖ ≤ B) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ S, ‖F z‖ ≤ C * (1 + ‖z‖) := by
  obtain ⟨M, hM⟩ := logDeriv_riemannZeta_bounded_of_two_le_re
  obtain ⟨Cd, hCd⟩ := hdig H
  set L : ℝ := ‖Complex.log (2 * (Real.pi : ℂ))‖ with hL_def
  set K : ℝ := |M| + L + (1 + Real.pi + |Cd| / 2) + (Real.pi / 2) * B + 1 with hK_def
  have hK : 0 ≤ K := by
    have : (0:ℝ) ≤ L := norm_nonneg _
    have hpi := Real.pi_pos
    positivity
  refine ⟨K + 1, by linarith, fun z hz ↦ ?_⟩
  have hre : z.re ≤ -1 := hS z hz
  have hz1 : z ≠ 1 := by intro h; rw [h] at hre; simp at hre; linarith
  -- `ζ z ≠ 0`: `hcos` rules out the even integers, hence every trivial zero.
  have hzne : riemannZeta z ≠ 0 := by
    refine riemannZeta_ne_zero_of_re_neg (by linarith) (fun n hn ↦ ?_)
    refine hcos z hz ?_
    rw [hn, Complex.cos_eq_zero_iff]
    exact ⟨(n : ℤ) + 1, by push_cast; ring⟩
  -- Rewrite `F` through the ladder-form identity.
  have hFz : F z = -(deriv riemannZeta z / riemannZeta z) - (z - 1)⁻¹ := by
    rw [F, logDeriv_riemannZeta₁_eq hz1 hzne, logDeriv_apply]
    ring
  have hlad := logDeriv_ladder_form hfe (by linarith : z.re < 0) (hcos z hz)
  rw [hFz, hlad]
  -- Bound the five terms.
  have hw2 : (2 : ℝ) ≤ (1 - z).re := by
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw2' : (2 : ℝ) ≤ ‖1 - z‖ := by
    have h := Complex.abs_re_le_norm (1 - z)
    have h' : (1 - z).re ≤ |(1 - z).re| := le_abs_self _
    linarith
  have hw1 : (1 : ℝ) ≤ ‖1 - z‖ := by linarith
  have hwle : ‖1 - z‖ ≤ 1 + ‖z‖ := by
    calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ := by simp
  have hzm1 : ‖z - 1‖ = ‖1 - z‖ := by rw [← norm_neg]; congr 1; ring
  have hinv : ‖(z - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv, inv_le_one_iff₀]
    right; rw [hzm1]; linarith
  have hdg : ‖Complex.digamma (1 - z)‖ ≤ (1 + ‖z‖ + Real.pi) + |Cd| / 2 := by
    have hsplit : Complex.digamma (1 - z)
        = (Complex.digamma (1 - z) - Complex.log (1 - z)) + Complex.log (1 - z) := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have him : |(1 - z).im| ≤ H := by
      simpa [Complex.sub_im, Complex.one_im, abs_neg] using hH z hz
    have h1 := hCd (1 - z) (by linarith) him
    have h2 := norm_log_le_norm_add_pi hw1
    have h3 : Cd / ‖1 - z‖ ≤ |Cd| / 2 := by
      by_cases hc : Cd ≤ 0
      · have hle : Cd / ‖1 - z‖ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc (by linarith)
        have hnn : (0:ℝ) ≤ |Cd| / 2 := by positivity
        linarith
      · push_neg at hc
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        have hab : Cd ≤ |Cd| := le_abs_self _
        nlinarith
    linarith
  have hX : ‖deriv riemannZeta (1 - z) / riemannZeta (1 - z)‖ ≤ |M| :=
    (hM (1 - z) hw2).trans (le_abs_self M)
  have hT : ‖((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * (1 - z) / 2)‖
      ≤ (Real.pi / 2) * B := by
    rw [norm_mul]
    have hnp : ‖((Real.pi : ℂ) / 2)‖ = Real.pi / 2 := by
      rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real]
      exact Real.norm_of_nonneg (by positivity)
    rw [hnp]
    exact mul_le_mul_of_nonneg_left (htan z hz) (by positivity)
  -- Expand into a five-term sum and peel the triangle inequality one term at a time.
  have hexpand : -(-(deriv riemannZeta (1 - z) / riemannZeta (1 - z))
        + Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma (1 - z)
        + ((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * (1 - z) / 2)) - (z - 1)⁻¹
      = deriv riemannZeta (1 - z) / riemannZeta (1 - z)
        + -Complex.log (2 * (Real.pi : ℂ))
        + Complex.digamma (1 - z)
        + -(((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * (1 - z) / 2))
        + -(z - 1)⁻¹ := by ring
  rw [hexpand]
  have hpeel : ‖deriv riemannZeta (1 - z) / riemannZeta (1 - z)
        + -Complex.log (2 * (Real.pi : ℂ))
        + Complex.digamma (1 - z)
        + -(((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * (1 - z) / 2))
        + -(z - 1)⁻¹‖
      ≤ ‖deriv riemannZeta (1 - z) / riemannZeta (1 - z)‖
        + ‖-Complex.log (2 * (Real.pi : ℂ))‖
        + ‖Complex.digamma (1 - z)‖
        + ‖-(((Real.pi : ℂ) / 2) * Complex.tan ((Real.pi : ℂ) * (1 - z) / 2))‖
        + ‖-(z - 1)⁻¹‖ := by
    refine le_trans (norm_add_le _ _) (add_le_add ?_ (le_refl _))
    refine le_trans (norm_add_le _ _) (add_le_add ?_ (le_refl _))
    refine le_trans (norm_add_le _ _) (add_le_add ?_ (le_refl _))
    exact norm_add_le _ _
  simp only [norm_neg] at hpeel
  refine hpeel.trans ?_
  have hznn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  have hLdef : ‖Complex.log (2 * (Real.pi : ℂ))‖ = L := hL_def.symm
  rw [hLdef, hK_def]
  nlinarith [hX, hdg, hT, hinv, hznn, norm_nonneg (Complex.log (2 * (Real.pi : ℂ)))]

/-! ### Assembling the far half

Placed here rather than beside the near half because it consumes `norm_F_le_linear`,
which is the last estimate in the file. -/

/-- **The far half of `prop_5_2`'s first boundedness hypothesis.**

The two estimates meet here: `norm_F_le_linear` gives `‖F z‖ = O(1 + ‖z‖)` from the functional
equation and the digamma bound, and `exists_bound_of_linear_growth_mul_cpow` turns that into a
genuine bound once multiplied by `x₀ ^ z`, because `Re z ≤ 0` makes that factor decay
exponentially and beat any linear growth.

The two lemmas share a constant, so one that serves both is taken: `max C l.T`, which is at least
the growth constant and at least the height. -/
theorem isBoundedNoPolesOn_farLadder
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    {l : CH2.LadderParams} (hσ : l.σ = sigmaZeta)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T)
    (hδfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.δ)
    {x₀ : ℝ} (hx₀ : 1 < x₀) :
    CH2.IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s)
      ((l.Rboundary ∪ l.admissible_contour ∪ l.L) ∩ {z : ℂ | z.re ≤ -1}) := by
  have hT : 0 < l.T := l.hT
  set S : Set ℂ := (l.Rboundary ∪ l.admissible_contour ∪ l.L) ∩ {z : ℂ | z.re ≤ -1} with hS_def
  have hSre : ∀ z ∈ S, z.re ≤ -1 := fun z hz ↦ hz.2
  have hSim : ∀ z ∈ S, |z.im| ≤ l.T := fun z hz ↦ abs_im_le_T_of_mem_ladder hz.1
  obtain ⟨B, hB, hBd⟩ := exists_tan_bound_on_farLadder l hσ
  have hcos : ∀ z ∈ S, Complex.cos ((Real.pi : ℂ) * (1 - z) / 2) ≠ 0 := fun z hz ↦
    cos_ne_zero_on_farLadder hσ hz.1 hz.2
  have htan : ∀ z ∈ S, ‖Complex.tan ((Real.pi : ℂ) * (1 - z) / 2)‖ ≤ B := fun z hz ↦
    hBd z hz.1 hz.2
  obtain ⟨C, hC, hCd⟩ := norm_F_le_linear hfe hdig hB hSre hSim hcos htan
  -- One constant for both lemmas.
  set C' : ℝ := max C l.T with hC'_def
  have hC' : 0 ≤ C' := le_trans hC (le_max_left _ _)
  have hbd : ∀ z ∈ S, ‖F z‖ ≤ C' * (1 + ‖z‖) := by
    intro z hz
    refine le_trans (hCd z hz) ?_
    have h1 : (0 : ℝ) ≤ 1 + ‖z‖ := by positivity
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) h1
  have hIm : ∀ z ∈ S, |z.im| ≤ C' := fun z hz ↦ le_trans (hSim z hz) (le_max_right _ _)
  obtain ⟨M, hM⟩ := exists_bound_of_linear_growth_mul_cpow hx₀ hC'
    (fun z hz ↦ by linarith [hSre z hz]) hbd hIm
  refine ⟨M, fun z hz ↦ ⟨hM z hz, ?_⟩⟩
  exact meromorphicOrderAt_nonneg_of_analyticAt
    ((analyticAt_F_of_mem_farLadder hσ hTfree hδfree hz.1 hz.2).mul
      (analyticAt_const_cpow (by linarith : (0:ℝ) < x₀) z))

/-- **`prop_5_2`'s first boundedness hypothesis, closed.**

The two halves meet: every point of the ladder has `Re z ≥ -1` or `Re z ≤ -1`, the first lands in
`nearLadder` by `nearLadder_covers` and is handled by compactness, the second by the growth bound.
This is the first of `prop_5_2`'s five outstanding hypotheses to be discharged outright. -/
theorem isBoundedNoPolesOn_ladder
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    {l : CH2.LadderParams} (hσ : l.σ = sigmaZeta)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T)
    (hδfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.δ)
    {x₀ : ℝ} (hx₀ : 1 < x₀) :
    CH2.IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s)
      (l.Rboundary ∪ l.admissible_contour ∪ l.L) := by
  have hcover : (l.Rboundary ∪ l.admissible_contour ∪ l.L)
      ⊆ nearLadder l.T l.δ ∪
        ((l.Rboundary ∪ l.admissible_contour ∪ l.L) ∩ {z : ℂ | z.re ≤ -1}) := by
    intro z hz
    rcases le_or_gt (-1 : ℝ) z.re with h | h
    · exact Or.inl (nearLadder_covers hσ ⟨hz, h⟩)
    · exact Or.inr ⟨hz, le_of_lt h⟩
  refine isBoundedNoPolesOn_mono ?_ hcover
  exact isBoundedNoPolesOn_union
    (isBoundedNoPolesOn_nearLadder hTfree hδfree (by linarith : (0:ℝ) < x₀))
    (isBoundedNoPolesOn_farLadder hfe hdig hσ hTfree hδfree hx₀)

/-- `‖zOf z‖ ≤ (1 + ‖z‖)/T`: the weight is linear, which is what turns `F`'s linear growth into
quadratic growth and forces `exists_bound_of_quadratic_growth_mul_cpow`. -/
theorem norm_zOf_le (l : CH2.LadderParams) (z : ℂ) : ‖l.zOf z‖ ≤ (1 + ‖z‖) / l.T := by
  have hT : 0 < l.T := l.hT
  have hnum : ‖z - 1‖ ≤ 1 + ‖z‖ := by
    refine (norm_sub_le z 1).trans ?_
    simp [add_comm]
  have hden : ‖Complex.I * (l.T : ℂ)‖ = l.T := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hT.le]
  show ‖(z - 1) / (Complex.I * (l.T : ℂ))‖ ≤ (1 + ‖z‖) / l.T
  rw [norm_div, hden]
  gcongr

/-- **The far half of `prop_5_2`'s second boundedness hypothesis.** -/
theorem isBoundedNoPolesOn_farLadder_weighted
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    {l : CH2.LadderParams} (hσ : l.σ = sigmaZeta)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T)
    (hδfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.δ)
    {x₀ : ℝ} (hx₀ : 1 < x₀) :
    CH2.IsBoundedNoPolesOn (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s)
      ((l.Rboundary ∪ l.admissible_contour ∪ l.L) ∩ {z : ℂ | z.re ≤ -1}) := by
  have hT : 0 < l.T := l.hT
  set S : Set ℂ := (l.Rboundary ∪ l.admissible_contour ∪ l.L) ∩ {z : ℂ | z.re ≤ -1} with hS_def
  have hSre : ∀ z ∈ S, z.re ≤ -1 := fun z hz ↦ hz.2
  have hSim : ∀ z ∈ S, |z.im| ≤ l.T := fun z hz ↦ abs_im_le_T_of_mem_ladder hz.1
  obtain ⟨B, hB, hBd⟩ := exists_tan_bound_on_farLadder l hσ
  have hcos : ∀ z ∈ S, Complex.cos ((Real.pi : ℂ) * (1 - z) / 2) ≠ 0 := fun z hz ↦
    cos_ne_zero_on_farLadder hσ hz.1 hz.2
  have htan : ∀ z ∈ S, ‖Complex.tan ((Real.pi : ℂ) * (1 - z) / 2)‖ ≤ B := fun z hz ↦
    hBd z hz.1 hz.2
  obtain ⟨C, hC, hCd⟩ := norm_F_le_linear hfe hdig hB hSre hSim hcos htan
  set C' : ℝ := max (C / l.T) l.T with hC'_def
  have hC' : 0 ≤ C' := le_trans (div_nonneg hC hT.le) (le_max_left _ _)
  have hbd : ∀ z ∈ S, ‖l.zOf z * F z‖ ≤ C' * (1 + ‖z‖) ^ 2 := by
    intro z hz
    have hnn : (0 : ℝ) ≤ 1 + ‖z‖ := by positivity
    rw [norm_mul]
    calc ‖l.zOf z‖ * ‖F z‖ ≤ ((1 + ‖z‖) / l.T) * (C * (1 + ‖z‖)) :=
          mul_le_mul (norm_zOf_le l z) (hCd z hz) (norm_nonneg _) (by positivity)
      _ = (C / l.T) * (1 + ‖z‖) ^ 2 := by field_simp
      _ ≤ C' * (1 + ‖z‖) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hIm : ∀ z ∈ S, |z.im| ≤ C' := fun z hz ↦ le_trans (hSim z hz) (le_max_right _ _)
  obtain ⟨M, hM⟩ := exists_bound_of_quadratic_growth_mul_cpow hx₀ hC'
    (fun z hz ↦ by linarith [hSre z hz]) hbd hIm
  refine ⟨M, fun z hz ↦ ⟨hM z hz, ?_⟩⟩
  exact meromorphicOrderAt_nonneg_of_analyticAt
    (((analyticAt_zOf l z).mul (analyticAt_F_of_mem_farLadder hσ hTfree hδfree hz.1 hz.2)).mul
      (analyticAt_const_cpow (by linarith : (0:ℝ) < x₀) z))

/-- **`prop_5_2`'s second boundedness hypothesis, closed.**

With this, both boundedness hypotheses are discharged and three of the five outstanding ones are
gone. What remains is `hfin` and the two `HasSimplePolesOn` conditions, which are about the
PRODUCT `Φ_λ(zOf s) · F s · x ^ s` rather than about `F`. -/
theorem isBoundedNoPolesOn_ladder_weighted
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    {l : CH2.LadderParams} (hσ : l.σ = sigmaZeta)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T)
    (hδfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.δ)
    {x₀ : ℝ} (hx₀ : 1 < x₀) :
    CH2.IsBoundedNoPolesOn (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s)
      (l.Rboundary ∪ l.admissible_contour ∪ l.L) := by
  have hcover : (l.Rboundary ∪ l.admissible_contour ∪ l.L)
      ⊆ nearLadder l.T l.δ ∪
        ((l.Rboundary ∪ l.admissible_contour ∪ l.L) ∩ {z : ℂ | z.re ≤ -1}) := by
    intro z hz
    rcases le_or_gt (-1 : ℝ) z.re with h | h
    · exact Or.inl (nearLadder_covers hσ ⟨hz, h⟩)
    · exact Or.inr ⟨hz, le_of_lt h⟩
  refine isBoundedNoPolesOn_mono ?_ hcover
  exact isBoundedNoPolesOn_union
    (isBoundedNoPolesOn_nearLadder_weighted hTfree hδfree (by linarith : (0:ℝ) < x₀))
    (isBoundedNoPolesOn_farLadder_weighted hfe hdig hσ hTfree hδfree hx₀)

end CH2ZetaInstance
