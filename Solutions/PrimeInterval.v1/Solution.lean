/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import IEANTN.Nodes.PrimeInterval.v1.Conclusions

/-!
# Solution: `PrimeInterval.v1`

Proves the same declarations `Challenge.lean` states. Does not import the challenge module.

Adapted from `PrimeNumberTheoremAnd/IEANTN/PrimeInInterval.lean` and `Defs.lean`
(AlexKontorovich/PrimeNumberTheoremAnd), restated against this repository's Vocabulary.
-/

open Real Finset Nat Chebyshev

namespace PrimeInterval.v1.Dev

theorem theta_characterisation (x h : ℝ) :
    IEANTN.HasPrimeInInterval x h ↔ θ (x + h) > θ x := by
  constructor
  · rintro ⟨p, hpprime, hxp, hpxh⟩
    let s : Finset ℕ := filter Nat.Prime (Icc 0 ⌊x⌋₊)
    let t : Finset ℕ := filter Nat.Prime (Icc 0 ⌊x + h⌋₊)
    have hxxh : x ≤ x + h := le_of_lt (lt_of_lt_of_le hxp hpxh)
    have hs : s ⊆ t := by
      intro q hq
      rw [mem_filter] at hq ⊢
      exact ⟨mem_Icc.mpr ⟨(mem_Icc.mp hq.1).1,
        le_trans (mem_Icc.mp hq.1).2 (Nat.floor_mono hxxh)⟩, hq.2⟩
    have hp_in_t : p ∈ t :=
      mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le p, Nat.le_floor hpxh⟩, hpprime⟩
    have hp_notin_s : p ∉ s := by
      intro hpins
      rw [mem_filter, mem_Icc] at hpins
      have hx_nn : 0 ≤ x := by
        have hfloor_pos : 0 < ⌊x⌋₊ := lt_of_lt_of_le hpprime.pos hpins.1.2
        exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (Nat.floor_pos.mp hfloor_pos)
      exact (not_le_of_gt hxp) ((Nat.cast_le.2 hpins.1.2).trans (Nat.floor_le hx_nn))
    have hnonneg : ∀ q ∈ t, q ∉ s → 0 ≤ Real.log q := by
      intro q hq _
      rw [mem_filter] at hq
      exact Real.log_nonneg (Nat.one_le_cast.2 hq.2.one_le)
    have hsum_lt : (∑ q ∈ s, Real.log q) < ∑ q ∈ t, Real.log q :=
      Finset.sum_lt_sum_of_subset hs hp_in_t hp_notin_s
        (Real.log_pos (Nat.one_lt_cast.2 hpprime.one_lt)) hnonneg
    simpa [Chebyshev.theta_eq_sum_Icc, s, t] using hsum_lt
  · intro htheta
    have hxh : x < x + h := by
      by_contra hle
      have hmono : θ (x + h) ≤ θ x := Chebyshev.theta_mono (le_of_not_gt hle)
      linarith
    let s : Finset ℕ := filter Nat.Prime (Icc 0 ⌊x⌋₊)
    let t : Finset ℕ := filter Nat.Prime (Icc 0 ⌊x + h⌋₊)
    have hs : s ⊆ t := by
      intro q hq
      rw [mem_filter] at hq ⊢
      exact ⟨mem_Icc.mpr ⟨(mem_Icc.mp hq.1).1,
        le_trans (mem_Icc.mp hq.1).2 (Nat.floor_mono hxh.le)⟩, hq.2⟩
    have hstrict : (∑ q ∈ s, Real.log q) < ∑ q ∈ t, Real.log q := by
      simpa [Chebyshev.theta_eq_sum_Icc, s, t] using htheta
    have hne : s ≠ t := fun heq ↦ absurd (heq ▸ hstrict) (lt_irrefl _)
    obtain ⟨p, hp_in_t, hp_notin_s⟩ := Finset.exists_of_ssubset (hs.ssubset_of_ne hne)
    rw [mem_filter, mem_Icc] at hp_in_t
    have hp_gt_floor_x : ⌊x⌋₊ < p := by
      by_contra hle
      exact hp_notin_s (mem_filter.mpr
        ⟨mem_Icc.mpr ⟨Nat.zero_le p, not_lt.mp hle⟩, hp_in_t.2⟩)
    have hxh_pos : 0 < ⌊x + h⌋₊ := lt_of_lt_of_le hp_in_t.2.pos hp_in_t.1.2
    have hxh_ge_one : (1 : ℝ) ≤ x + h := Nat.floor_pos.mp hxh_pos
    refine ⟨p, hp_in_t.2, ?_, ?_⟩
    · calc x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
        _ ≤ p := by exact_mod_cast hp_gt_floor_x
    · calc (p : ℝ) ≤ ⌊x + h⌋₊ := by exact_mod_cast hp_in_t.1.2
        _ ≤ x + h := Nat.floor_le (by linarith)

theorem eTheta_criterion (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    x * IEANTN.Eθ x + (x + h) * IEANTN.Eθ (x + h) < h → IEANTN.HasPrimeInInterval x h := by
  intro hE
  have hxh : 0 < x + h := by linarith
  have hx_bound : θ x ≤ x + x * IEANTN.Eθ x := by
    have hx_abs : x * IEANTN.Eθ x = |θ x - x| := by
      unfold IEANTN.Eθ; field_simp [hx.ne']
    have habs : |θ x - x| ≤ x * IEANTN.Eθ x := by simp [hx_abs]
    linarith [abs_sub_le_iff.mp habs |>.1]
  have hxh_bound : (x + h) - (x + h) * IEANTN.Eθ (x + h) ≤ θ (x + h) := by
    have hxh_abs : (x + h) * IEANTN.Eθ (x + h) = |θ (x + h) - (x + h)| := by
      unfold IEANTN.Eθ; field_simp [hxh.ne']
    have habs : |θ (x + h) - (x + h)| ≤ (x + h) * IEANTN.Eθ (x + h) := by simp [hxh_abs]
    linarith [abs_sub_le_iff.mp habs |>.2]
  exact (theta_characterisation x h).2 (by linarith)

theorem numericalBound_hasPrimeInInterval (x₀ x h ε : ℝ)
    (hEθ : IEANTN.HasNumericalBound IEANTN.Eθ ε x₀) (hh : 0 < h) (hx₀ : x₀ ≤ x) (hx : 0 < x)
    (hε : (2 * x + h) * ε < h) : IEANTN.HasPrimeInInterval x h := by
  have hxh : 0 < x + h := by linarith
  have hE₁ : IEANTN.Eθ x ≤ ε := hEθ x hx₀
  have hE₂ : IEANTN.Eθ (x + h) ≤ ε := hEθ (x + h) (by linarith)
  have h1 : x * IEANTN.Eθ x ≤ x * ε := mul_le_mul_of_nonneg_left hE₁ hx.le
  have h2 : (x + h) * IEANTN.Eθ (x + h) ≤ (x + h) * ε :=
    mul_le_mul_of_nonneg_left hE₂ hxh.le
  have hsum : x * IEANTN.Eθ x + (x + h) * IEANTN.Eθ (x + h) ≤ (2 * x + h) * ε := by nlinarith
  exact eTheta_criterion x h hx hh (lt_of_le_of_lt hsum hε)

/-- For positive parameters, `admissibleBound` is antitone on the ray beginning at
`exp (R * (2 * B / C) ^ 2)`, where the bound reaches its maximum. -/
theorem admissibleBound_mono
    (A B C R : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hR : 0 < R) :
    AntitoneOn (IEANTN.admissibleBound A B C R) (Set.Ici (Real.exp (R * (2 * B / C) ^ 2))) := by
  intro a ha b _ hab
  simp only [IEANTN.admissibleBound, mul_assoc]
  have hua : (2 * B / C) ^ 2 ≤ Real.log a / R := by
    rw [le_div_iff₀ hR, mul_comm ((2 * B / C) ^ 2), ← Real.log_exp (R * (2 * B / C) ^ 2)]
    exact Real.log_le_log (Real.exp_pos _) (Set.mem_Ici.mp ha)
  have huab : Real.log a / R ≤ Real.log b / R :=
    div_le_div_of_nonneg_right
      (Real.log_le_log ((Real.exp_pos _).trans_le (Set.mem_Ici.mp ha)) hab) hR.le
  have hua₀ : 0 < Real.log a / R := lt_of_lt_of_le (by positivity) hua
  apply mul_le_mul_of_nonneg_left _ hA.le
  rw [Real.rpow_def_of_pos (hua₀.trans_le huab), Real.rpow_def_of_pos hua₀,
    ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  set sa := (Real.log a / R) ^ ((1 : ℝ) / 2) with hsa_def
  set sb := (Real.log b / R) ^ ((1 : ℝ) / 2) with hsb_def
  have hlogb : Real.log (Real.log b / R) = 2 * Real.log sb := by
    rw [hsb_def, Real.log_rpow (hua₀.trans_le huab)]; ring
  have hloga : Real.log (Real.log a / R) = 2 * Real.log sa := by
    rw [hsa_def, Real.log_rpow hua₀]; ring
  rw [hlogb, hloga]
  have hsab : sa ≤ sb :=
    Real.rpow_le_rpow (le_trans (by positivity) hua) huab (by positivity)
  have hthr : 2 * B / C ≤ sa := by
    rw [show (2 * B / C : ℝ) = ((2 * B / C) ^ 2) ^ ((1 : ℝ) / 2) from by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
      norm_num]
    exact Real.rpow_le_rpow (by positivity) hua (by positivity)
  suffices h : AntitoneOn (fun t ↦ 2 * B * Real.log t - C * t) (Set.Ici (2 * B / C)) by
    have := h (Set.mem_Ici.mpr hthr) (Set.mem_Ici.mpr (hthr.trans hsab)) hsab
    simp only at this
    linarith
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact ((continuousOn_const.mul (Real.continuousOn_log.mono fun t ht ↦
        ne_of_gt ((div_pos (by positivity) hC).trans_le ht))).sub
      (continuousOn_const.mul continuousOn_id))
  · intro t ht
    rw [interior_Ici] at ht
    exact (((Real.hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
      ((hasDerivAt_id t).const_mul C)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hdt : HasDerivAt (fun t ↦ 2 * B * Real.log t - C * t) (2 * B * t⁻¹ - C * 1) t :=
      ((Real.hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
        ((hasDerivAt_id t).const_mul C)
    rw [hdt.deriv, mul_one, sub_nonpos, ← div_eq_mul_inv,
      div_le_iff₀ ((div_pos (by positivity) hC).trans ht)]
    linarith [(div_lt_iff₀ hC).mp ht, mul_comm C t]

theorem classicalBound_hasPrimeInInterval (x₀ x h A B C R : ℝ)
    (hEθ : IEANTN.HasClassicalBound IEANTN.Eθ A B C R x₀)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hR : 0 < R) (hh : 0 < h) (hx : x₀ ≤ x)
    (hx' : x ≥ Real.exp (R * (2 * B / C) ^ 2))
    (hb : (2 * x + h) * IEANTN.admissibleBound A B C R x < h) :
    IEANTN.HasPrimeInInterval x h := by
  have hx_mem : x ∈ Set.Ici (Real.exp (R * (2 * B / C) ^ 2)) := Set.mem_Ici.mpr hx'
  have hnum : IEANTN.HasNumericalBound IEANTN.Eθ (IEANTN.admissibleBound A B C R x) x := by
    intro y hy
    have hy_mem : y ∈ Set.Ici (Real.exp (R * (2 * B / C) ^ 2)) :=
      Set.mem_Ici.mpr (hx'.trans hy)
    exact le_trans (hEθ y (hx.trans hy)) (admissibleBound_mono A B C R hA hB hC hR hx_mem hy_mem hy)
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx'
  exact numericalBound_hasPrimeInInterval x x h (IEANTN.admissibleBound A B C R x) hnum hh le_rfl
    hx_pos hb

end PrimeInterval.v1.Dev

theorem PrimeInterval.v1.challenge_theta_characterisation :
    PrimeInterval.v1.theta_characterisation :=
  PrimeInterval.v1.Dev.theta_characterisation

theorem PrimeInterval.v1.challenge_eTheta_criterion : PrimeInterval.v1.eTheta_criterion :=
  PrimeInterval.v1.Dev.eTheta_criterion

theorem PrimeInterval.v1.challenge_numericalBound_hasPrimeInInterval :
    PrimeInterval.v1.numericalBound_hasPrimeInInterval :=
  PrimeInterval.v1.Dev.numericalBound_hasPrimeInInterval

theorem PrimeInterval.v1.challenge_classicalBound_hasPrimeInInterval :
    PrimeInterval.v1.classicalBound_hasPrimeInInterval :=
  PrimeInterval.v1.Dev.classicalBound_hasPrimeInInterval
