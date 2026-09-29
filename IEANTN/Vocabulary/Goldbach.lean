/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Vocabulary: the Goldbach conjectures, verified up to a height

The two predicates in which numerical verifications of Goldbach are stated, and in which the
reductions between them are proved. Five nodes mention them, which is why they are here.

Both are statements *up to a finite height*, which is the only form in which either conjecture is
a theorem. Neither says anything about the conjecture itself.
-/

namespace IEANTN

/-- `GoldbachEvenUpTo H`: every even `n` with `4 ≤ n ≤ H` is a sum of two primes.

The even Goldbach conjecture, verified to height `H`. The lower endpoint is `4` because `2` is not
a sum of two primes; `4 = 2 + 2` is the first case.

**Vacuous below the lower endpoint.** For `H < 4` the range `Finset.Icc 4 H` is empty, so
`GoldbachEvenUpTo H` holds trivially — true rather than false, and a conclusion stating it at a
small `H` asserts nothing. The interesting content is entirely in how large `H` is.

The two primes need not be distinct, and no ordering is imposed. -/
def GoldbachEvenUpTo (H : ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 4 H, Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- `GoldbachOddUpTo H`: every odd `n` with `7 ≤ n ≤ H` is a sum of three primes.

The odd Goldbach conjecture — Vinogradov's ternary problem — verified to height `H`. The lower
endpoint is `7 = 3 + 2 + 2`, the first odd number that is a sum of three primes.

Vacuous for `H < 7`, for the same reason as `GoldbachEvenUpTo`. The three primes need not be
distinct.

Note that this is *not* the form in which Helfgott's theorem settles the odd case: that is a
statement for all `n`, proved by an analytic argument above a finite height and by verification
below it. This predicate is the verification half. -/
def GoldbachOddUpTo (H : ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 7 H, Odd n →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

end IEANTN
