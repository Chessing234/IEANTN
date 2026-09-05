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

example (h : PrimeInterval.v1.classicalBound_hasPrimeInInterval)
    (hC : IEANTN.HasClassicalBound IEANTN.Eθ 1 1 1 1 (Real.exp 4))
    (hb : (2 * Real.exp 4 + 1) * IEANTN.admissibleBound 1 1 1 1 (Real.exp 4) < 1) :
    IEANTN.HasPrimeInInterval (Real.exp 4) 1 :=
  h (Real.exp 4) (Real.exp 4) 1 1 1 1 1 hC (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) le_rfl (by norm_num) hb

end PrimeInterval.v1.Examples
