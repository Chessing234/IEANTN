/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import ChebyshevDev
import IEANTN.Nodes.Chebyshev.v1.Conclusions
import IEANTN.Nodes.ChebyshevNumerics.v1.Conclusions

/-!
# Solution for `Chebyshev.v1`

The five conclusions, each from the corresponding theorem in `ChebyshevDev`, which is the port of
`PrimeNumberTheoremAnd/IEANTN/Chebyshev.lean`. Nothing is proved in this file: it is the seam
between the node's statements and the development's, and the only work in it is identifying the
node's constant `a` with the development's.

`challenge_psi_upper_clean` is the conditional one. It takes
`ChebyshevNumerics.v1.psi_le_below_11723` as a hypothesis, exactly as the generated challenge
supplies it, and hands it to the induction as its base case.
-/

open Real

namespace ChebyshevSol

/-- The node defines Chebyshev's constant by the closed form; the development defines it as
`−Σ ν(m) log m / m` and derives the closed form in `a_simpl`. They are the same real number. -/
theorem a_eq_node : ChebyshevSol.a = Chebyshev.v1.a := by
  rw [ChebyshevSol.a_simpl]
  rfl

end ChebyshevSol

theorem Chebyshev.v1.challenge_constant_bounds : Chebyshev.v1.constant_bounds := by
  have h := ChebyshevSol.a_bound
  rw [Set.mem_Icc, ChebyshevSol.a_eq_node] at h
  exact ⟨by norm_num at h ⊢; linarith [h.1], by norm_num at h ⊢; linarith [h.2]⟩

theorem Chebyshev.v1.challenge_psi_lower : Chebyshev.v1.psi_lower := by
  intro x hx
  have h := ChebyshevSol.psi_lower x hx
  rw [ChebyshevSol.a_eq_node] at h
  exact h

theorem Chebyshev.v1.challenge_psi_upper : Chebyshev.v1.psi_upper := by
  intro x hx
  have h := ChebyshevSol.psi_upper x hx
  rw [ChebyshevSol.a_eq_node] at h
  exact h

theorem Chebyshev.v1.challenge_psi_le_small : Chebyshev.v1.psi_le_small := by
  intro x hx hx30
  exact ChebyshevSol.psi_num x hx hx30

theorem Chebyshev.v1.challenge_psi_upper_clean
    (chebyshevnumerics_v1_psi_le_below_11723 : ChebyshevNumerics.v1.psi_le_below_11723) :
    Chebyshev.v1.psi_upper_clean := by
  intro x hx
  exact ChebyshevSol.psi_upper_clean chebyshevnumerics_v1_psi_le_below_11723 x hx
