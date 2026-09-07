/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The vanishing lemma

A 1-periodic function that vanishes at the naturals and varies by `O(1/n)` across unit intervals
far out is identically zero on the positive reals.

This is the whole content of identifying `ψ` with its Gauss series on the reals, isolated from the
series so it can be checked on its own. Periodicity lets any point be pushed arbitrarily far
right, where the oscillation bound is arbitrarily tight and a zero of `E` always sits within
distance one.

**The naive version — `E` vanishes at the naturals and is periodic, therefore zero — does not
work, and believing it cost this project a wrong claim in an earlier draft of the node
docstring**: periodicity spreads `E 1 = 0` to the integers and nowhere else. A 1-periodic function
vanishing on `ℤ` is otherwise entirely unconstrained. The oscillation hypothesis is what reaches
between the integers, and it is supplied on both sides by Stage 1 (`ψ` fluctuates by `O(1/x)`
across a unit interval) and by a telescoping comparison for the series.

Nothing here is about `Γ`; it is a statement about real functions, and it is stated that way
deliberately so that the analytic input and the soft argument can be audited apart.
-/

namespace GammaSolution

/-- **A 1-periodic function vanishing at the naturals, with `O(1/n)` oscillation, is zero.** -/
theorem eq_zero_of_periodic_of_nat_of_oscillation {E : ℝ → ℝ} {C : ℝ}
    (hper : Function.Periodic E 1)
    (hnat : ∀ n : ℕ, E ((n : ℝ) + 1) = 0)
    (hosc : ∀ n : ℕ, 1 ≤ n → ∀ a b : ℝ, (n : ℝ) ≤ a → (n : ℝ) ≤ b → |a - b| ≤ 1 →
      |E a - E b| ≤ C / n)
    {x : ℝ} (hx : 0 < x) : E x = 0 := by
  have key : ∀ n : ℕ, 1 ≤ n → |E x| ≤ C / n := by
    intro n hn
    set m : ℕ := ⌊x⌋₊ with hm
    have hmx : (m : ℝ) ≤ x := Nat.floor_le hx.le
    have hxm : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    -- Push `x` right by `n`; compare with the zero of `E` at `m + n + 1`.
    have hEx : E x = E (x + n) := by simpa using (hper.nat_mul n x).symm
    have hzero : E (((m + n : ℕ) : ℝ) + 1) = 0 := hnat (m + n)
    have hle_a : (n : ℝ) ≤ x + n := by linarith
    have hle_b : (n : ℝ) ≤ ((m + n : ℕ) : ℝ) + 1 := by push_cast; linarith
    have hclose : |(x + n) - (((m + n : ℕ) : ℝ) + 1)| ≤ 1 := by
      push_cast
      rw [abs_le]
      constructor <;> linarith
    have hb := hosc n hn (x + n) (((m + n : ℕ) : ℝ) + 1) hle_a hle_b hclose
    rwa [hzero, sub_zero, ← hEx] at hb
  -- `C / n → 0`, so a quantity below all of them is at most zero.
  have hlim : Filter.Tendsto (fun n : ℕ ↦ C / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hle : |E x| ≤ 0 :=
    ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨1, fun n hn ↦ key n hn⟩)
  exact abs_nonpos_iff.mp hle

end GammaSolution
