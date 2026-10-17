/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Goldbach
import IEANTN.Vocabulary.PrimeGaps

/-!
# Node `Goldbach.v1` — from even Goldbach to odd Goldbach

The reductions that turn a verification of the *even* Goldbach conjecture into a verified range for
the *odd* one, and the three ranges that follow from the verifications and prime-gap results this
network holds.

## The idea, in one line

To write an odd `n` as three primes, take a prime `p` just below `n`; then `n − p` is even, and
small enough for a verification to cover.

How small depends on how short an interval is guaranteed to contain a prime. With no such result
one can only subtract `3`, which is `even_implies_odd` and gains nothing. With a prime in
`(x(1 − 1/Δ), x]` one can subtract a prime within `x/Δ` of `n`, so a verification to `H` covers odd
numbers up to about `HΔ` — a factor of `Δ`, and `Δ` here is in the billions.

## What is proved and what is assumed

The first three conclusions import nothing: they are theorems about the predicates, true whatever
the state of any computation. The last three import the verification and prime-gap nodes, and are
the arithmetic of putting particular numbers through the second one.

None of this proves the Goldbach conjecture, or any case of it beyond what the imported
computations already establish. What it does is make the conversion explicit and checkable, so that
a better verification of even Goldbach — or a narrower prime interval — yields a better odd range by
re-instantiating rather than by re-arguing.
-/

namespace Goldbach.v1

open IEANTN

/-- **Subtracting three.** If even Goldbach holds to `H`, odd Goldbach holds to `H + 3`.

The trivial reduction: an odd `n ≤ H + 3` has `n − 3` even and at most `H`, so `n = p + q + 3`.
It gains nothing asymptotically and is exactly what is needed at the bottom of the range, below the
threshold where any short-interval result applies. -/
def even_implies_odd : Prop :=
  ∀ H : ℕ, GoldbachEvenUpTo H → GoldbachOddUpTo (H + 3)

/-- **The reduction that gains a factor of `Δ`.**

If every natural `x ≥ x₀` has a prime in `(x(1 − 1/Δ), x]`, even Goldbach holds to `H`, and odd
Goldbach holds to `x₀ + 4`, then odd Goldbach holds to `(H − 4)Δ + 4`.

The `x₀ + 4` hypothesis covers the bottom of the range, where the interval result does not yet
apply; `even_implies_odd` supplies it in practice. The `− 4` and `+ 4` are the two ends of the even
range: `n − p` must be at least `4` to be a sum of two primes, and at most `H`.

**The casts are written out on purpose.** `Δ` is a natural number, so `1 / Δ` read in `ℕ` would be
`0` for every `Δ ≥ 2`, and the hypothesis would degenerate into "every interval `(x, x]` contains a
prime" — unsatisfiable, and a conclusion resting on it would say nothing. What makes it right is
that `HasPrimeInInterval` takes reals, so the division is real; writing `(Δ : ℝ)` makes that
visible rather than leaving it to elaboration and the reader's attention. -/
def even_and_gaps_imply_odd : Prop :=
  ∀ x₀ H Δ : ℕ,
    (∀ x : ℕ, x₀ ≤ x →
      HasPrimeInInterval ((x : ℝ) * (1 - 1 / (Δ : ℝ))) ((x : ℝ) / (Δ : ℝ))) →
    GoldbachEvenUpTo H → GoldbachOddUpTo (x₀ + 4) →
    GoldbachOddUpTo ((H - 4) * Δ + 4)

/-- **Even Goldbach to 30, by hand.** Every even `n` with `4 ≤ n ≤ 30` is a sum of two primes.

Fourteen cases, each a pair of primes. Trivial, and worth stating: it is the base case that starts
the ladder, and the one part of the subject that needs no computation to trust. -/
def even_up_to_30 : Prop :=
  GoldbachEvenUpTo 30

/-- **Odd Goldbach to `11 325 599 999 999 886 744 004 ≈ 1.13·10²²`**, from Richstein's
verification and Ramaré–Saouter's intervals.

Ramaré and Saouter state a range of this size themselves, in their Corollary 1. Here it is derived
rather than cited: `Richstein2001.v1` to `4·10¹⁴`, stretched by the factor `28 314 000` their
short-interval result provides. The number is exactly `(4·10¹⁴ − 4)·28 314 000 + 4`. -/
def odd_up_to_ramare_saouter : Prop :=
  GoldbachOddUpTo ((4 * 10 ^ 14 - 4) * 28314000 + 4)

/-- **Odd Goldbach to `1.1325·10²⁶`**, from the `4·10¹⁸` verification and Ramaré–Saouter.

The same conversion with the better verification, rounded down to a readable number from the
`(4·10¹⁸ − 4)·28 314 000 + 4` the reduction gives. Helfgott's Appendix C states a range of this
size; his own argument goes further using unpublished estimates of Ramaré, which is why this is
named for the number rather than for him. -/
def odd_up_to_1_1325e26 : Prop :=
  GoldbachOddUpTo (11325 * 10 ^ 22)

/-- **Odd Goldbach to `(4·10¹⁸ − 4)·1 966 196 911 + 4 ≈ 7.86·10²⁷`**, from the `4·10¹⁸`
verification and Kadiri–Lumley's intervals.

The best range the network's inputs support: the same verification, stretched by `1 966 196 911`
instead of `28 314 000`. Kadiri and Lumley state a range of this size as their Corollary 1.2.

It rests on Ramaré–Saouter as well, which the statement does not show. Kadiri and Lumley's rows
begin at `exp 59 ≈ 4.2·10²⁵` and the even verification reaches `4·10¹⁸`; something has to carry the
odd range across that gap, and only the wider Ramaré–Saouter intervals do.

Not the rounder `1 966 196 911·4·10¹⁸` that PrimeNumberTheoremAnd reaches. The difference is the
four integers between `4·10¹⁸` and `4·10¹⁸ + 4`, which PNT+ covers by proving two nineteen-digit
numbers prime with Pocklington certificates from a package outside Mathlib. The gap is about
`8·10⁹` out of `7.9·10²⁷` — a relative `10⁻¹⁸` — and not worth an external dependency. -/
def odd_up_to_kadiri_lumley : Prop :=
  GoldbachOddUpTo ((4 * 10 ^ 18 - 4) * 1966196911 + 4)

end Goldbach.v1
