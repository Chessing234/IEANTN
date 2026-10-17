/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Node `Chebyshev.v1` — Chebyshev's elementary bounds on `ψ`

The classical elementary estimates: `ψ(x)` is bounded above and below by a constant multiple of
`x`, with an explicit constant and an explicit error term, and with no analytic input at all — no
zero-free region, no verification height, no zero density estimate.

**This node imports nothing, and that is a real `none`.** Every other bound on `ψ` in this network
is conditional on something: a computation, a zero-free region, a paper's own numerics. These are
not. They are the floor the rest of the network sits on, and a consumer can use them knowing that
what backs them is a Lean proof from Mathlib rather than a citation.

## The argument, in one paragraph

Following Chebyshev, and the presentation in Diamond's survey: put `T(x) = Σ_{n ≤ x} log n`, which
Stirling-type integral comparison pins to `x log x − x + 1` within `log x`. The identity
`log n = Σ_{d ∣ n} Λ(d)` turns `T` into `Σ_{n ≤ x} Λ(n) ⌊x/n⌋`, so a finitely supported weight `ν`
produces `Σ_m ν(m) T(x/m) = Σ_{n ≤ x} Λ(n) E(x/n)` with `E(y) = Σ_m ν(m) ⌊y/m⌋`. Chebyshev's
weight `ν = e₁ − e₂ − e₃ − e₅ + e₃₀` makes `E` take values in `{0, 1}` — it is `1` on `[1, 6)` and
has period `30` — which sandwiches `ψ` between `U(x) = Σ_m ν(m) T(x/m)` and `U(x) + ψ(x/6)`. The
constant `a` below is `−Σ_m ν(m) log m / m`, which is what `U(x)/x` tends to.

## The one conclusion that is not unconditional

`psi_upper_clean`, the sharp form `ψ(x) ≤ 1.11 x` for all `x > 0`, imports
`ChebyshevNumerics.v1`. The induction proving it steps from `x` to `x/6` and closes only above
`x = 11723`; everything below is a finite check, which PrimeNumberTheoremAnd does with
`native_decide` — `Lean.ofReduceBool`, which Comparator does not admit. So the check is a node of
its own and this conclusion is a conditional theorem: *if* `ψ(n) ≤ 1.11 n` for the integers below
`11723`, *then* it holds for every real `x > 0`. The analytic half is proved here; the arithmetic
half is named rather than hidden.
-/

namespace Chebyshev.v1

open Real

/-- **Chebyshev's constant** `a = (7/15) log 2 + (3/10) log 3 + (1/6) log 5 ≈ 0.9212920`.

This is `−Σ_m ν(m) log m / m` for Chebyshev's weight `ν = e₁ − e₂ − e₃ − e₅ + e₃₀`, which collects
to the displayed form because `log 30 = log 2 + log 3 + log 5`. Equivalently
`a = log (2^{7/15} · 3^{3/10} · 5^{1/6})`.

Not a conclusion — a definition the three conclusions below share, kept here rather than in
Vocabulary because nothing outside this node has any use for it. `constant_bounds` pins it
numerically. -/
noncomputable def a : ℝ := (7 / 15) * log 2 + (3 / 10) * log 3 + (1 / 6) * log 5

/-- **The numerical value of `a`**: `0.92129 ≤ a ≤ 0.92130`.

Stated so that a consumer of `psi_lower` and `psi_upper` can use them without re-deriving the
constant. Both bounds are strict in the mathematics; the closed form is stated because it is what
a proof produces and what a reader can check. -/
def constant_bounds : Prop :=
  0.92129 ≤ a ∧ a ≤ 0.92130

/-- **Chebyshev's lower bound.** For every `x ≥ 30`,

`ψ(x) ≥ a x − 5 log x + 5`.

Unconditional, and in particular `ψ(x) ≥ 0.92129 x − 5 log x + 5` by `constant_bounds`. The `+5`
rather than the `−1` that a reader might expect from a cruder accounting of the error is what the
weight `ν` actually delivers: `|U(x) − a x| ≤ 5 log x − 5` on `x ≥ 30`, and `ψ ≥ U` there. -/
def psi_lower : Prop :=
  ∀ x : ℝ, 30 ≤ x → a * x - 5 * log x + 5 ≤ Chebyshev.psi x

/-- **Chebyshev's upper bound.** For every `x ≥ 30`,

`ψ(x) ≤ 6 a x / 5 + (log(x/5) / log 6) (5 log x − 5)`.

The shape is what iterating `ψ(x) − ψ(x/6) ≤ a x + 5 log x − 5` down to the base case produces:
the geometric sum of `a x / 6^i` contributes `6 a x / 5`, and the number of steps, `log(x/5)/log 6`,
multiplies the error term. `6a/5 = 1.10555…`, so this is weaker than the `1.11 x` the module
docstring discusses only by the second term, which is `O(log x ^ 2)`.

The `log 6` in the denominator is harmless: `log 6 > 0`, so nothing here is a junk value. -/
def psi_upper : Prop :=
  ∀ x : ℝ, 30 ≤ x →
    Chebyshev.psi x ≤ 6 * a * x / 5 + (log (x / 5) / log 6) * (5 * log x - 5)

/-- **The small range.** For every `0 < x ≤ 30`, `ψ(x) ≤ 1.015 x`.

A finite check — `ψ` is a step function with jumps at the prime powers below 30 — stated as a
conclusion because it is the base case anything iterating `psi_upper`'s step downwards will need,
and because 1.015 is sharper on this range than any of the asymptotic constants. The extremal
point is `x = 19`, where `ψ(19) = 19.2657…` against `1.015 · 19 = 19.285`. -/
def psi_le_small : Prop :=
  ∀ x : ℝ, 0 < x → x ≤ 30 → Chebyshev.psi x ≤ 1.015 * x

/-- **The clean upper bound.** `ψ(x) ≤ 1.11 x` for every `x > 0`.

No threshold, no error term — the form a consumer actually wants, and the sharpest constant this
elementary argument reaches. `6a/5 = 1.10555…` is what the iteration gives in the limit, and
`1.11` is what survives carrying the error term down to the base case.

**Conditional, and the only conditional conclusion on this node.** It imports
`ChebyshevNumerics.v1.psi_le_below_11723`, the finite check below the point where the induction
becomes self-sustaining. See the module docstring for why that check is a node rather than a
lemma. What is proved here is the implication, which is all of the mathematics and none of the
arithmetic. -/
def psi_upper_clean : Prop :=
  ∀ x : ℝ, 0 < x → Chebyshev.psi x ≤ 1.11 * x

end Chebyshev.v1
