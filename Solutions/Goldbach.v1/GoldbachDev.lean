/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Nodes.Goldbach.v1.Conclusions
import Mathlib

/-!
# From even Goldbach to odd Goldbach

Ported from `PrimeNumberTheoremAnd/IEANTN/Goldbach.lean`. The mathematics and the tactic scripts
are that development's; what changed is the surroundings.

* The LeanArchitect metadata is gone, and the two predicates are the network's Vocabulary ones.
* The two verifications PNT+ states with `sorry` are nodes here — `Richstein2001.v1` and
  `OliveiraESilva2014.v1` — so the three range theorems below take them as hypotheses instead.
  Same for the two prime-gap results, `RamareSaouter2003.v1` and `KadiriLumley.v1`.
* `interval_decide`, which is LeanCert's, is replaced by `exp_le_pow` below.
* PNT+'s extension of the `4·10¹⁸` verification to `4·10¹⁸ + 4` is not ported: it needs Pocklington
  certificates from the external `PrimeCert` package. The Kadiri–Lumley range is therefore stated
  from `4·10¹⁸`, which costs a relative `10⁻¹⁸`.
-/

namespace GoldbachSol

open IEANTN Finset

/-! ### The two reductions -/

theorem even_mono (H H' : ℕ) (h : GoldbachEvenUpTo H) (hh : H' ≤ H) : GoldbachEvenUpTo H' := by
  intro n hn
  apply h
  grind

theorem odd_mono (H H' : ℕ) (h : GoldbachOddUpTo H) (hh : H' ≤ H) : GoldbachOddUpTo H' := by
  intro n hn
  apply h
  grind

/-- Even Goldbach to `H` gives odd Goldbach to `H + 3`: subtract the prime `3`. -/
theorem even_implies_odd (H : ℕ) (h : GoldbachEvenUpTo H) : GoldbachOddUpTo (H + 3) := by
  intro n hn ⟨k, hk⟩
  simp only [Finset.mem_Icc] at hn
  obtain ⟨p, q, hp, hq, hpq⟩ := h (n - 3)
    (by simp only [Finset.mem_Icc]; omega) ⟨k - 1, by omega⟩
  exact ⟨p, q, 3, hp, hq, Nat.prime_three, by omega⟩

/-- Even Goldbach to 30, by hand: fourteen cases. -/
theorem even_up_to_30 : GoldbachEvenUpTo 30 := by
  intro n hn he
  fin_cases hn
  all_goals try grind
  · exact ⟨2, 2, by decide⟩
  · exact ⟨3, 3, by decide⟩
  · exact ⟨3, 5, by decide⟩
  · exact ⟨5, 5, by decide⟩
  · exact ⟨5, 7, by decide⟩
  · exact ⟨7, 7, by decide⟩
  · exact ⟨5, 11, by decide⟩
  · exact ⟨7, 11, by decide⟩
  · exact ⟨7, 13, by decide⟩
  · exact ⟨11, 11, by decide⟩
  · exact ⟨11, 13, by decide⟩
  · exact ⟨13, 13, by decide⟩
  · exact ⟨11, 17, by decide⟩
  · exact ⟨13, 17, by decide⟩

theorem odd_up_to_33 : GoldbachOddUpTo 33 := even_implies_odd 30 even_up_to_30

/-- **The reduction that gains a factor of `Δ`.** PNT+'s proof, verbatim apart from
names: `hprime` is its hypothesis with the coercions written out. -/
theorem even_and_gaps_imply_odd (x₀ H Δ : ℕ)
    (hprime : ∀ x : ℕ, x₀ ≤ x →
      HasPrimeInInterval ((x : ℝ) * (1 - 1 / (Δ : ℝ))) ((x : ℝ) / (Δ : ℝ)))
    (heven : GoldbachEvenUpTo H) (hodd : GoldbachOddUpTo (x₀ + 4)) :
    GoldbachOddUpTo ((H - 4) * Δ + 4) := by
  by_cases! hH : H < 4
  · simp_all [tsub_eq_zero_of_le hH.le, GoldbachOddUpTo]
  by_cases! Δ ≤ 1
  · interval_cases Δ
    · simp_all [GoldbachOddUpTo]
    · simp_all [odd_mono (H + 3) H (even_implies_odd H heven) (by linarith)]
  · intro n h ho
    by_cases! hn33 : n ≤ 8
    · exact odd_up_to_33 n (by grind : n ∈ Finset.Icc 7 33) ho
    by_cases! hn : n ≤ x₀ + 4
    · exact hodd n (by grind : n ∈ Finset.Icc 7 (x₀ + 4)) ho
    · obtain ⟨p, hp⟩ := hprime (n - 4) (by grind : n - 4 ≥ x₀)
      have hnpe : Even (n - p) :=
        have h2p : 2 < p := by
          rw [← Nat.cast_lt (α := ℝ)]
          calc
          _ = (8 - 4) * (1 - 1 / 2 : ℝ) := by norm_num
          _ < (n - 4) * (1 -  1 / 2 : ℝ) := by gcongr; norm_cast
          _ ≤ ↑(n - 4) * (1 -  1 / Δ : ℝ) := by gcongr <;> norm_cast; grind
          _ < p := hp.2.1
        ho.tsub_odd (hp.1.odd_of_ne_two h2p.ne')
      have hnp : (n - p) ∈ Finset.Icc 4 H := by
        have hpn4 : p ≤ n - 4 := by simpa [field] using hp.2.2
        have hpn : p ≤ n := hpn4.trans tsub_le_self
        refine Finset.mem_Icc.2 ⟨?_, ?_⟩
        · exact (le_tsub_iff_le_tsub (by grind) hpn).2 hpn4
        · have := hp.2.1
          rw [← Nat.cast_le (α := ℝ), Nat.cast_sub hpn]
          rw [Nat.cast_sub (by grind), mul_sub, mul_one, ← sub_add_eq_sub_sub,
            sub_lt_comm] at this
          refine this.le.trans ?_
          calc
          _ ≤ 4 + ((↑(H - 4) * Δ + 4) - 4) * (1 / Δ : ℝ) := by gcongr <;> norm_cast; grind
          _ ≤ _ := by simp [field, Nat.cast_sub hH]
      obtain ⟨q, r, hqr⟩ := heven (n - p) hnp hnpe
      refine ⟨p, q, r, hp.1, hqr.1, hqr.2.1, ?_⟩
      grind

/-! ### `exp` at an integer, replacing LeanCert's `interval_decide` -/

/-- `exp n ≤ 2.7182818286 ^ n`, from Mathlib's bound on `e`. -/
theorem exp_le_pow (n : ℕ) : Real.exp n ≤ (2.7182818286 : ℝ) ^ n := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n

/-! ### The three ranges

Each takes its inputs as hypotheses: the node supplies them as imports. -/

/-- Odd Goldbach to `(4·10¹⁴ − 4)·28 314 000 + 4`, from Richstein and Ramaré–Saouter. -/
theorem odd_up_to_ramare_saouter
    (richstein : GoldbachEvenUpTo (4 * 10 ^ 14))
    (rs : ∀ x : ℝ, 10726905041 < x →
      HasPrimeInInterval (x * (1 - 1 / 28314000)) (x / 28314000)) :
    GoldbachOddUpTo ((4 * 10 ^ 14 - 4) * 28314000 + 4) := by
  have h1 := even_and_gaps_imply_odd 10726905042 (4 * 10 ^ 14) 28314000
    (fun x hx => rs x (by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hx)) richstein
  exact h1 (odd_mono _ _ (even_implies_odd _ richstein) (by norm_num))

/-- Odd Goldbach to `1.1325·10²⁶`, from the `4·10¹⁸` verification and Ramaré–Saouter. -/
theorem odd_up_to_1_1325e26
    (eshp : GoldbachEvenUpTo (4 * 10 ^ 18))
    (rs : ∀ x : ℝ, 10726905041 < x →
      HasPrimeInInterval (x * (1 - 1 / 28314000)) (x / 28314000)) :
    GoldbachOddUpTo (11325 * 10 ^ 22) := by
  have h1 := even_and_gaps_imply_odd 10726905042 (4 * 10 ^ 18) 28314000
    (fun x hx => rs x (by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hx)) eshp
  exact odd_mono _ _ (h1 (odd_mono _ _ (even_implies_odd _ eshp) (by norm_num))) (by norm_num)

/-- Odd Goldbach to `(4·10¹⁸ − 4)·1 966 196 911 + 4`, from the `4·10¹⁸` verification and the two
Kadiri–Lumley rows. Both rows are needed: the `exp 60` one is sharper but applies only above
`exp 60`, and the `exp 59` one carries the range up to that point. -/
theorem odd_up_to_kadiri_lumley
    (eshp : GoldbachEvenUpTo (4 * 10 ^ 18))
    (kl59 : ∀ x : ℝ, Real.exp 59 ≤ x →
      ∃ p : ℕ, Nat.Prime p ∧ x * (1 - 1 / 1946282821) < p ∧ (p : ℝ) < x)
    (kl60 : ∀ x : ℝ, Real.exp 60 ≤ x →
      ∃ p : ℕ, Nat.Prime p ∧ x * (1 - 1 / 1966196911) < p ∧ (p : ℝ) < x)
    (rs : ∀ x : ℝ, 10726905041 < x →
      HasPrimeInInterval (x * (1 - 1 / 28314000)) (x / 28314000)) :
    GoldbachOddUpTo ((4 * 10 ^ 18 - 4) * 1966196911 + 4) := by
  -- An open-right interval gives the closed-right one, since `x(1-1/Δ) + x/Δ = x`.
  have close {Δ : ℝ} (hΔ : 0 < Δ) {x : ℝ}
      (h : ∃ p : ℕ, Nat.Prime p ∧ x * (1 - 1 / Δ) < p ∧ (p : ℝ) < x) :
      HasPrimeInInterval (x * (1 - 1 / Δ)) (x / Δ) := by
    obtain ⟨p, hp, hlo, hhi⟩ := h
    refine ⟨p, hp, hlo, ?_⟩
    have hΔ0 : Δ ≠ 0 := ne_of_gt hΔ
    have : x * (1 - 1 / Δ) + x / Δ = x := by field_simp; ring
    rw [this]
    exact hhi.le
  -- Step one: up to `exp 59`, using Ramaré–Saouter via the Helfgott range.
  have base := odd_up_to_1_1325e26 eshp rs
  have e59 : Real.exp 59 ≤ 4.3e25 := (exp_le_pow 59).trans (by norm_num)
  have h59 : (⌈Real.exp 59⌉₊ : ℕ) + 4 ≤ 11325 * 10 ^ 22 := by
    have : ⌈Real.exp 59⌉₊ ≤ 11325 * 10 ^ 22 - 4 :=
      Nat.ceil_le.mpr (by push_cast; linarith)
    omega
  have step59 := even_and_gaps_imply_odd ⌈Real.exp 59⌉₊ (4 * 10 ^ 18) 1946282821
    (fun x hx => close (by norm_num) (kl59 x (Nat.ceil_le.mp hx))) eshp (odd_mono _ _ base h59)
  -- Step two: from there, the sharper `exp 60` row.
  have e60 : Real.exp 60 ≤ 1.2e26 := (exp_le_pow 60).trans (by norm_num)
  have h60 : (⌈Real.exp 60⌉₊ : ℕ) + 4 ≤ (4 * 10 ^ 18 - 4) * 1946282821 + 4 := by
    have : ⌈Real.exp 60⌉₊ ≤ (4 * 10 ^ 18 - 4) * 1946282821 :=
      Nat.ceil_le.mpr (by push_cast; linarith)
    omega
  have step60 := even_and_gaps_imply_odd ⌈Real.exp 60⌉₊ (4 * 10 ^ 18) 1966196911
    (fun x hx => close (by norm_num) (kl60 x (Nat.ceil_le.mp hx))) eshp
    (odd_mono _ _ step59 h60)
  exact step60

end GoldbachSol
