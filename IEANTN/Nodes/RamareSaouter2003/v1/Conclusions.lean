/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.PrimeGaps

/-!
# Node `RamareSaouter2003.v1` — a prime in every short interval above `1.07·10¹⁰`

Ramaré and Saouter's explicit short-interval result: above `10 726 905 041`, the interval
`(x(1 − 1/28 314 000), x]` always contains a prime. The width is proportional to `x`, not to
`x/(log x)^k`, which is what makes it usable in an induction that divides by a constant.

This is the input that turns a verification of *even* Goldbach into a range for *odd* Goldbach:
given a prime just below `n`, what is left over is even and small enough to be covered by the
verification. `Goldbach.v1` does that step.
-/

namespace RamareSaouter2003.v1

open IEANTN

/-- **A prime in `(x(1 − 1/Δ), x]` for `x > 10 726 905 041`**, with `Δ = 28 314 000`.

Stated with the network's `HasPrimeInInterval`, which is closed on the right — matching the
paper's own `(x(1 − 1/Δ), x]`, as PrimeNumberTheoremAnd also transcribes it. The half-open
convention is not incidental: an interval closed at both ends would be a different claim at `x`
itself.

The threshold is exact, not rounded: `10 726 905 041` is the paper's own. -/
def prime_in_short_interval : Prop :=
  ∀ x : ℝ, 10726905041 < x →
    HasPrimeInInterval (x * (1 - 1 / 28314000)) (x / 28314000)

end RamareSaouter2003.v1
