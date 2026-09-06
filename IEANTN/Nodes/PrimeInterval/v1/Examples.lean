/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import IEANTN.Nodes.PrimeInterval.v1.Conclusions

/-!
# Examples: `PrimeInterval.v1`

One consequence per conclusion, taken as a hypothesis, to show what each statement buys.
-/

namespace PrimeInterval.v1.Examples

example (h : PrimeInterval.v1.theta_characterisation)
    (hjump : Chebyshev.theta (100 + 1) > Chebyshev.theta 100) :
    IEANTN.HasPrimeInInterval 100 1 :=
  (h 100 1).2 hjump

example (h : PrimeInterval.v1.eTheta_criterion)
    (hE : (100 : ℝ) * IEANTN.Eθ 100 + (100 + 1) * IEANTN.Eθ (100 + 1) < 1) :
    IEANTN.HasPrimeInInterval 100 1 :=
  h 100 1 (by norm_num) (by norm_num) hE

example (h : PrimeInterval.v1.numericalBound_hasPrimeInInterval)
    (hε : IEANTN.HasNumericalBound IEANTN.Eθ 0.001 100) :
    IEANTN.HasPrimeInInterval 100 1 :=
  h 100 100 1 0.001 hε (by norm_num) le_rfl (by norm_num) (by norm_num)

/-- The classical-bound pipeline at the parameters `FKS2.v2.proposition_13` produces
(`A = 121.0961`, `B = 3/2`, `C = 2`, `R = 5.5666305`, `x₀ = exp 30`). The admissibility
inequality `hb` stays a hypothesis: at any concrete `x` it is a transcendental evaluation
(`Real.rpow`, `Real.exp`) that `norm_num` cannot decide, so no numeral is asserted here. What
the example checks is that the binders line up. -/
example (h : PrimeInterval.v1.classicalBound_hasPrimeInInterval) (x : ℝ)
    (hC : IEANTN.HasClassicalBound IEANTN.Eθ 121.0961 (3 / 2) 2 5.5666305 (Real.exp 30))
    (hx : Real.exp 30 ≤ x)
    (hx' : x ≥ Real.exp (5.5666305 * (2 * (3 / 2) / 2) ^ 2))
    (hb : (2 * x + 1) * IEANTN.admissibleBound 121.0961 (3 / 2) 2 5.5666305 x < 1) :
    IEANTN.HasPrimeInInterval x 1 :=
  h (Real.exp 30) x 1 121.0961 (3 / 2) 2 5.5666305 hC (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx hx' hb

end PrimeInterval.v1.Examples
