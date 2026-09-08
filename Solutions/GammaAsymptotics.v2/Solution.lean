/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import RealAsymptotic
import Periodic
import GaussSeries
import Recurrence
import RealIdentity
import Analytic
import Strip
import IEANTN.Nodes.GammaAsymptotics.v2.Conclusions

/-!
# Solution: `GammaAsymptotics.v2`

**Complete.** No holes; the conclusion is proved under `propext`, `Classical.choice` and
`Quot.sound` alone. Comparator is the next step and is what would justify the node — nothing here
justifies anything on its own. `python scripts/ieantn.py progress GammaAsymptotics.v2` derives that
mechanically; `progress.yaml` carries the plan and what each stage cost.

## The route

The node's own docstring says both versions need the Gauss/Weierstrass representation

  `ψ(u) = -γ + ∑_{k≥0} (1/(k+1) - 1/(k+u))`,

which Mathlib lists as a `TODO`. That is still the target, and it is still the honest description
of what is missing — but the *real-variable asymptotic* turned out not to need it, which changes
the order of work. The plan is now:

1. **`|ψ(x) − log x| ≤ 1/x` on the reals**, from log-convexity alone. `RealAsymptotic.lean`.
   **Done**, with the constant explicit and equal to `1`.
2. **The Gauss series on `ℂ`.** Write `G s := -γ + ∑ₖ gaussTerm s k`.
   * a. the series converges — `GaussSeries.lean`, **done**;
   * b. the recurrence `G(s+1) = G(s) + 1/s` — `Recurrence.lean`, **done**, by telescoping;
   * d. hence `E := ψ - G` reproduces itself under `x ↦ x + 1` for `x > 0` —
        `RealIdentity.lean`, **done**;
   * e. `ψ(n+1) = G(n+1)`, both being `-γ + Hₙ` — `Recurrence.lean`, **done**;
   * f. `E` oscillates by `≤ 5/n` across unit intervals — `Oscillation.lean`, **done**: Stage 1
        gives the `ψ` side `3/n` (through `ComplexToReal.lean`), and a telescoping comparison
        gives the `G` side `2/n`;
   * **so `ψ = G` on the positive reals** — `RealIdentity.lean`, **done**, by
     `eq_zero_of_periodic_of_nat_of_oscillation`. *This is the Gauss representation, the fact
     Mathlib's `Digamma.lean` lists as a `TODO`, and the obstruction the node docstring named.*
   * c. `G` is analytic on the right half-plane — `Analytic.lean`, **done**, from
        `Complex.differentiableOn_tsum_of_summable_norm` and a bound uniform on a neighbourhood;
   * g. the identity theorem carries `ψ = G` from the positive reals, which accumulate at `1`, to
        the whole right half-plane — `Analytic.lean`, **done**.
   **Stage 2 is complete**: `digamma_eq_gaussSum` gives `ψ(s) = -γ + ∑ₖ (1/(k+1) - 1/(k+s))`
   whenever `Re s > 0`.
3. **The strip bound** — `Strip.lean`, **done**. Everything goes through the real point directly
   to the left, `u := Re w`, where Stage 1 already has the answer:
   `ψ(w) - log w = (ψ(w) - ψ(u)) + (ψ(u) - log u) + (log u - log w)`, the three pieces being
   `2|Im w|/u` from differencing the series, `1/u` from Stage 1, and `|Im w|/u` from the mean
   value inequality. That gives `(1 + 3|Im w|)/u`, and `u ≥ 1` turns `1/u` into `(1+H)/‖w‖`, so
   `C = (1 + 3H)(1 + H)`.

Step (c) moved after the real identity rather than before it, because nothing up to and including
the identity needs `G` to be analytic — the whole argument runs on the real axis, where `G` is
just a convergent series of real terms. Analyticity is needed only to *transport* the identity,
which is step (g)'s business.

**The transport is to the right half-plane, not the slit plane `ℂ \ {0,-1,-2,…}`.** The identity
is true on the latter and the restriction is deliberate: `Re s > 0` is everything the conclusion
needs, and on a half-plane the uniform bound the series lemma wants is one line, because
`‖k + s‖ ≥ Re (k + s) = k + Re s`. `Analytic.lean` records what the slit-plane version would take.

## What the shape of the finished proof says

The two steps that looked hardest going in — the real asymptotic and the periodic-vanishing
argument — were the two that finished first, and neither used the representation. What was
actually awkward was neither: it was `ComplexToReal.lean`, one lemma relating `Complex.digamma` on
the real axis to Stage 1's real derivative, whose Mathlib counterpart exists but is `private`.

**No derivative of `ψ` appears anywhere in this solution.** Both places that might have wanted one
— the oscillation bound of Stage 2f and the horizontal step of Stage 3 — instead *difference the
series*, where the divergent `1/(k+1)` cancels and what is left is `O(1/k²)` summing to `O(1/n)`.
Differentiating the series termwise would have needed `hasSum_deriv_of_summable_norm` and a second
uniform bound; it was never necessary.

## What the constant does

The conclusion quantifies `C` after `H`, so the constant may depend on the height and does. That
dependence is the entire difference between this node and `GammaAsymptotics.v1`, which asks for
one constant on the whole half-plane and is left open on purpose.
-/

theorem GammaAsymptotics.v2.challenge_digamma_sub_log_isBigO_strip :
    GammaAsymptotics.v2.digamma_sub_log_isBigO_strip :=
  GammaSolution.digamma_sub_log_strip
