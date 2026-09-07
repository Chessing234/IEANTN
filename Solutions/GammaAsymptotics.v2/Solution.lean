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
import IEANTN.Nodes.GammaAsymptotics.v2.Conclusions

/-!
# Solution: `GammaAsymptotics.v2`

**Incomplete.** One hole, the conclusion itself. What is proved and what is not is set out below
and derived mechanically by `python scripts/ieantn.py progress GammaAsymptotics.v2`; see
`progress.yaml` for the plan.

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
   * c. `G` is analytic off the non-positive integers — **to do**;
   * g. the identity theorem carries `ψ = G` from the positive reals, which have a limit point,
        to all of `ℂ` — **to do**, and needs (c).
3. **The strip bound.** With the representation in hand, `‖ψ w - log w‖ ≤ C_H / ‖w‖` for
   `Re w ≥ 1`, `|Im w| ≤ H` — **to do**.

Step (c) moved after the real identity rather than before it, because nothing up to and including
the identity needs `G` to be analytic — the whole argument runs on the real axis, where `G` is
just a convergent series of real terms. Analyticity is needed only to *transport* the identity,
which is step (g)'s business.

The two steps that looked hardest going in — the real asymptotic and the periodic-vanishing
argument — were the two that finished first, and neither used the representation. What was
actually awkward was neither: it was `ComplexToReal.lean`, one lemma relating `Complex.digamma` on
the real axis to Stage 1's real derivative, whose Mathlib counterpart exists but is `private`.

## What the constant does

The conclusion quantifies `C` after `H`, so the constant may depend on the height and does. That
dependence is the entire difference between this node and `GammaAsymptotics.v1`, which asks for
one constant on the whole half-plane and is left open on purpose.
-/

theorem GammaAsymptotics.v2.challenge_digamma_sub_log_isBigO_strip :
    GammaAsymptotics.v2.digamma_sub_log_isBigO_strip := by
  sorry
