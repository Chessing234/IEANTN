/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Numerical bounds on `log p` for the small primes

PrimeNumberTheoremAnd gets these from `LogTables.lean`, whose entries are proved by LeanCert's
`interval_decide`. That is not available here: a Comparator receipt admits only `propext`,
`Classical.choice` and `Quot.sound`, and the solution may not reach outside Mathlib. So this file
reproves what the port needs, from Mathlib's `exp_one_gt_d9` / `exp_one_lt_d9` and the Taylor
bounds for `exp`.

The recipe is one line of arithmetic: to place `log p` against a rational `c`, split `c = m + f`
with `m` a natural number and `f ∈ [0, 1)`, and bound `exp (m + f) = (exp 1) ^ m * exp f` above and
below, taking twelve Taylor terms for `exp f`. Twelve is not tuned: the tail at `f < 1` is below
`1 / 12!`, which is `2 · 10⁻⁹`, and the tightest bound here needs `10⁻⁷`.

Accuracy is chosen per consumer, not uniformly. `a`'s numerical value needs seven digits from
`log 2`, `log 3` and `log 5`, because `constant_bounds` pins `a` inside a window of `10⁻⁵` and the
three coefficients sum to about `0.95`. The bound `psi x ≤ 1.015 x` on `x ≤ 30` needs far less —
its worst case is `x = 19`, with `0.019` of room spread over eight logarithms — so five digits do
for the larger primes.

`log 2` is not proved here: Mathlib's `log_two_gt_d9` and `log_two_lt_d9` are sharper than anything
this file would produce.
-/

namespace ChebyshevSol

open Real

/-! ### Taylor bounds for `exp` -/

/-- Twelve Taylor terms, as a lower bound for `exp` on `[0, ∞)`: the omitted terms are positive. -/
theorem exp_ge_taylor {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 + x ^ 7 / 5040
        + x ^ 8 / 40320 + x ^ 9 / 362880 + x ^ 10 / 3628800 + x ^ 11 / 39916800 ≤ exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 12
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

/-- Twelve Taylor terms plus `Real.exp_bound'`'s remainder, as an upper bound on `[0, 1]`. -/
theorem exp_le_taylor {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 + x ^ 7 / 5040
        + x ^ 8 / 40320 + x ^ 9 / 362880 + x ^ 10 / 3628800 + x ^ 11 / 39916800
        + x ^ 12 * 13 / 5748019200 := by
  have h := Real.exp_bound' h0 h1 (n := 12) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

/-! ### `exp` at `m + f`, split as `(exp 1) ^ m * exp f` -/

/-- A lower bound for `exp (m + f)`: `e ^ m` from Mathlib, `exp f` from twelve Taylor terms. -/
theorem exp_lb (m : ℕ) {f : ℝ} (hf : 0 ≤ f) :
    (2.7182818283 : ℝ) ^ m * (1 + f + f ^ 2 / 2 + f ^ 3 / 6 + f ^ 4 / 24 + f ^ 5 / 120
        + f ^ 6 / 720 + f ^ 7 / 5040 + f ^ 8 / 40320 + f ^ 9 / 362880 + f ^ 10 / 3628800
        + f ^ 11 / 39916800) ≤ exp ((m : ℝ) + f) := by
  rw [Real.exp_add, ← Real.exp_one_pow]
  have hm : (2.7182818283 : ℝ) ^ m ≤ exp 1 ^ m :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le m
  exact mul_le_mul hm (exp_ge_taylor hf) (by positivity) (by positivity)

/-- An upper bound for `exp (m + f)`, for `f ∈ [0, 1]`. -/
theorem exp_ub (m : ℕ) {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    exp ((m : ℝ) + f) ≤ (2.7182818286 : ℝ) ^ m * (1 + f + f ^ 2 / 2 + f ^ 3 / 6 + f ^ 4 / 24
        + f ^ 5 / 120 + f ^ 6 / 720 + f ^ 7 / 5040 + f ^ 8 / 40320 + f ^ 9 / 362880
        + f ^ 10 / 3628800 + f ^ 11 / 39916800 + f ^ 12 * 13 / 5748019200) := by
  rw [Real.exp_add, ← Real.exp_one_pow]
  have hm : exp 1 ^ m ≤ (2.7182818286 : ℝ) ^ m :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le m
  exact mul_le_mul hm (exp_le_taylor h0 h1) (Real.exp_pos _).le (by positivity)

/-! ### The table

Upper bounds for every prime below `30`, and lower bounds for the three that `a` is built from.
Each is `log p ⋚ c` rewritten as `p ⋚ exp c` and then discharged by `norm_num` against `exp_lb` or
`exp_ub`. -/

theorem log_three_lt : log 3 < 1.0986123 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num),
    show (1.0986123 : ℝ) = ((1 : ℕ) : ℝ) + 0.0986123 by norm_num]
  exact lt_of_lt_of_le (by norm_num) (exp_lb 1 (by norm_num))

theorem log_three_gt : (1.0986122 : ℝ) < log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num),
    show (1.0986122 : ℝ) = ((1 : ℕ) : ℝ) + 0.0986122 by norm_num]
  exact lt_of_le_of_lt (exp_ub 1 (by norm_num) (by norm_num)) (by norm_num)

theorem log_five_lt : log 5 < 1.6094380 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num),
    show (1.6094380 : ℝ) = ((1 : ℕ) : ℝ) + 0.6094380 by norm_num]
  exact lt_of_lt_of_le (by norm_num) (exp_lb 1 (by norm_num))

theorem log_five_gt : (1.6094379 : ℝ) < log 5 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num),
    show (1.6094379 : ℝ) = ((1 : ℕ) : ℝ) + 0.6094379 by norm_num]
  exact lt_of_le_of_lt (exp_ub 1 (by norm_num) (by norm_num)) (by norm_num)

theorem log_seven_lt : log 7 < 1.94592 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num),
    show (1.94592 : ℝ) = ((1 : ℕ) : ℝ) + 0.94592 by norm_num]
  exact lt_of_lt_of_le (by norm_num) (exp_lb 1 (by norm_num))

theorem log_eleven_lt : log 11 < 2.3979 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num),
    show (2.3979 : ℝ) = ((2 : ℕ) : ℝ) + 0.3979 by norm_num]
  exact lt_of_lt_of_le (by norm_num) (exp_lb 2 (by norm_num))

theorem log_thirteen_lt : log 13 < 2.56495 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num),
    show (2.56495 : ℝ) = ((2 : ℕ) : ℝ) + 0.56495 by norm_num]
  exact lt_of_lt_of_le (by norm_num) (exp_lb 2 (by norm_num))

theorem log_seventeen_lt : log 17 < 2.83322 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num),
    show (2.83322 : ℝ) = ((2 : ℕ) : ℝ) + 0.83322 by norm_num]
  exact lt_of_lt_of_le (by norm_num) (exp_lb 2 (by norm_num))

theorem log_nineteen_lt : log 19 < 2.94444 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num),
    show (2.94444 : ℝ) = ((2 : ℕ) : ℝ) + 0.94444 by norm_num]
  exact lt_of_lt_of_le (by norm_num) (exp_lb 2 (by norm_num))

theorem log_twentythree_lt : log 23 < 3.1355 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num),
    show (3.1355 : ℝ) = ((3 : ℕ) : ℝ) + 0.1355 by norm_num]
  exact lt_of_lt_of_le (by norm_num) (exp_lb 3 (by norm_num))

theorem log_twentynine_lt : log 29 < 3.3673 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num),
    show (3.3673 : ℝ) = ((3 : ℕ) : ℝ) + 0.3673 by norm_num]
  exact lt_of_lt_of_le (by norm_num) (exp_lb 3 (by norm_num))

/-- `log 11723 ≤ 9.37`, the one entry not about a prime.

`11723` is where the induction in `psi_upper_clean` can first carry itself: the step needs
`1.11/6 + a + (5 log x − 5)/x ≤ 1.11`, and with `a ≤ 0.92130` that leaves `37/10000` for the last
term, which `x = 11723` is exactly the point of. `LogTables` proves this one too. -/
theorem log_11723_lt : log 11723 ≤ 9.37 := by
  rw [Real.log_le_iff_le_exp (by norm_num),
    show (9.37 : ℝ) = ((9 : ℕ) : ℝ) + 0.37 by norm_num]
  exact le_trans (by norm_num) (exp_lb 9 (by norm_num))

end ChebyshevSol
