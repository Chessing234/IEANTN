/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import RealAsymptotic
import Periodic
import GaussSeries
import Recurrence
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
   * c. `G` is analytic off the non-positive integers;
   * d. hence `E := ψ - G` is 1-periodic on the reals;
   * e. `ψ(n+1) = G(n+1)`, both being `-γ + Hₙ` — `Recurrence.lean`, **done**;
   * f. `E` oscillates by `O(1/n)` across unit intervals — Stage 1 handles the `ψ` side, a
        telescoping comparison the `G` side — so `eq_zero_of_periodic_of_nat_of_oscillation`
        (`Periodic.lean`, **done**) gives `E ≡ 0` on the positive reals;
   * g. the identity theorem carries `ψ = G` from a set with a limit point to all of `ℂ`.
3. **The strip bound.** With the representation in hand, `‖ψ w - log w‖ ≤ C_H / ‖w‖` for
   `Re w ≥ 1`, `|Im w| ≤ H`.

The two steps that looked hardest going in — the real asymptotic and the periodic-vanishing
argument — are the two that were finished first, and neither used the representation.

Of the vanishing lemma's three hypotheses, two are now in hand (2b gives periodicity once paired
with `Complex.digamma_apply_add_one`; 2e is the vanishing at integers outright). The oscillation
bound, 2f, is the one still to write, and Stage 1 already supplies its harder half.

## What the constant does

The conclusion quantifies `C` after `H`, so the constant may depend on the height and does. That
dependence is the entire difference between this node and `GammaAsymptotics.v1`, which asks for
one constant on the whole half-plane and is left open on purpose.
-/

theorem GammaAsymptotics.v2.challenge_digamma_sub_log_isBigO_strip :
    GammaAsymptotics.v2.digamma_sub_log_isBigO_strip := by
  sorry
