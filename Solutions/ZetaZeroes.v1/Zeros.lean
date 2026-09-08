/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib

/-!
# The zero set of `ζ`, and the `riemannZeta₁` bridge

Migrated verbatim from `Solutions/CH2.v1/ZetaInstance`, where these were proved because a ladder
argument needed them. Nothing in them is specific to that paper, which is why `ZetaZeroes.v1`
states them.

The only edits are mechanical: the surrounding namespace, and docstrings that referred to the
ladder now refer to a contour generally. No proof changed.
-/

open Complex Filter Topology

namespace ZetaZeroesSolution

/-- **The only zeroes of `ζ` in the left half-plane are the trivial ones.**

The proof is the functional equation and nothing else. Writing `s = 1 - w` with `Re w > 1`,
`riemannZeta_one_sub` expresses `ζ(s)` as a product of `2`, `(2π)^{-w}`, `Γ(w)`, `cos(πw/2)` and
`ζ(w)`. Every factor but the cosine is nonzero for free — `Γ` never vanishes, and `ζ(w) ≠ 0`
because `Re w > 1` — so `ζ(s) = 0` forces `cos(πw/2) = 0`, hence `w = 2k+1` and `s = -2k`, and
`Re s < 0` makes `k` positive. That is the trivial zeroes exactly.

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

end ZetaZeroesSolution
