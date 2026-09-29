/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.Chebyshev

/-!
# Node `ChebyshevNumerics.v1` — the finite check behind `ψ(x) ≤ 1.11 x`

One conclusion, and it is a computation: `ψ(n) ≤ 1.11 n` for every integer `n ≤ 11723`.

## Why this is a node rather than a lemma

`Chebyshev.v1.psi_upper_clean` is `ψ(x) ≤ 1.11 x` for **all** `x > 0`. Its proof is a strong
induction that steps from `x` to `x/6`, and the step closes only once `5 log x − 5 ≤ (37/10000) x`,
which first holds around `x = 11723`. Everything below that has to be checked.

The check is not hard, it is just large: `ψ` is a step function, and the assertion is eleven
thousand comparisons. PrimeNumberTheoremAnd does it with an `O(N)` incremental checker from
LeanCert, evaluated by `native_decide` — which is `Lean.ofReduceBool`, an axiom Comparator does not
admit. Reproving it inside the kernel is possible in principle and unattractive in practice.

So it is split off here, exactly as `BKLNWNumerics.v1` and `FKS2Numerics.v1` split off what their
papers computed rather than proved. The gain is that the *analytic* half of the `1.11` bound —
the induction, which is the mathematics — gets a Lean proof and a Comparator receipt, conditional
on this one finite statement, and the part no kernel checks is named in the graph instead of
hidden inside a solution.

## What would retire it

Two routes, both open.

* **Rosser and Schoenfeld** prove `ψ(x) < 1.03883 x` for every `x > 0` (1962, Theorem 12; Büthe
  quotes it in exactly that form). That is strictly stronger than this conclusion and would make
  this a `literature` node, or let a bridge discharge it, the moment `RosserSchoenfeld.v1` states
  it. That node exists and currently states nothing.
* **A kernel-checkable computation.** Nothing here needs `native_decide` in principle; an interval
  or certificate-based proof inside the kernel would turn this into an ordinary solution.

Until one of those, this is `numerical`: computed, not checked.
-/

namespace ChebyshevNumerics.v1

/-- **`ψ(n) ≤ 1.11 n` for every integer `n ≤ 11723`.**

Stated over `ℕ` because that is what the computation ranges over — `ψ` is constant between
consecutive integers, so the real-variable form follows from this one by monotonicity, and a
consumer that wants it can do that step in Lean.

`11723` is not a round number and not tuned here: it is where
`1.11/6 + a + (5 log x − 5)/x ≤ 1.11` first holds, with `a = 0.921292…` Chebyshev's constant. The
inequality is comfortable at every `n` in range — the true maximum of `ψ(n)/n` is `1.03883…`, at
`n = 113` — so the `1.11` has room; what it does not have is a proof short enough to want inline. -/
def psi_le_below_11723 : Prop :=
  ∀ n : ℕ, (n : ℝ) ≤ 11723 → Chebyshev.psi n ≤ 1.11 * n

end ChebyshevNumerics.v1
