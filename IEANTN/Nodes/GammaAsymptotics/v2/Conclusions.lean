/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Node `GammaAsymptotics.v2`

The digamma asymptotic `ψ(w) = log w + O(1/|w|)`, **restricted to a horizontal strip**.

## Why a second version rather than an edit

`GammaAsymptotics.v1` states the same estimate on the whole half-plane `Re w ≥ 1`. That statement
is true and remains the thing worth having; it is retained, unproved, as the harder target. What
this version does is impose a bound on `|Im w|`, which is what makes the estimate reachable.

The split is forced by two separate constraints, and both are worth stating because neither is
obvious:

* **Verification is all-or-nothing per node.** `record_receipt` refuses unless `comparator.json`
  covers every conclusion, so a provable statement bundled with a deliberately-open one could
  never receive a receipt. The strip therefore cannot live beside the half-plane version.
* **`v1` is imported**, so editing it in place is refused by *Network impact*.

## Why the strip is the honest boundary, not a convenience

`v1`'s recorded route — iterate `digamma_apply_add_one` from a compact box in `Re w ∈ [1, 2]` —
**does not prove `v1`**. It pushes rightward and controls `Re w → ∞` at bounded height; it says
nothing about `w = 1 + it` as `t → ∞`, which no compact box reaches. Closing the half-plane
version needs a Binet or Gauss integral representation, and Mathlib has neither: its `Digamma`
file is sixty-four lines, and `BohrMollerup`'s `logGammaSeq` is real-variable only.

So the strip is exactly the region the elementary argument covers. `v1` was not merely
over-general; it was over-general in the direction that carries all the difficulty.

## What the consumer needs

`CH2.v1` evaluates `ψ` only at `1 - s` for `s` on the ladder, and every piece of that set —
`Rboundary`, the admissible contour, the columns `L` — has `|Im s| ≤ T`. So the strip is not a
compromise for that consumer; it is everything it ever asked for.

**A future project is to remove the height restriction**, which means proving `v1`. That is a
genuine piece of complex analysis and a plausible Mathlib contribution in its own right.
-/

namespace GammaAsymptotics.v2

/-- **Digamma is `log` up to `O(1/|w|)` on a horizontal strip.**

For each height `H` there is a constant, depending on `H`, with
`‖ψ w - log w‖ ≤ C / ‖w‖` whenever `1 ≤ Re w` and `|Im w| ≤ H`.

The constant is allowed to depend on `H` and that dependence is the whole point: a bound uniform
in `H` is `GammaAsymptotics.v1`, which is why that version is stated separately and left open.

Imports nothing: `w` is universally quantified with every condition a hypothesis, so a Lean proof
is this conclusion's whole justification. -/
def digamma_sub_log_isBigO_strip : Prop :=
  ∀ H : ℝ, ∃ C : ℝ, ∀ w : ℂ, 1 ≤ w.re → |w.im| ≤ H →
    ‖Complex.digamma w - Complex.log w‖ ≤ C / ‖w‖

end GammaAsymptotics.v2
