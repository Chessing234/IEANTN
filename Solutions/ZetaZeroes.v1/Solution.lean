/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Zeros
import IEANTN.Nodes.ZetaZeroes.v1.Conclusions

/-!
# Solution: `ZetaZeroes.v1`

Each conclusion is one application of a lemma in `Zeros.lean`, which is the migrated body of
`Solutions/CH2.v1/ZetaInstance`. The node states; that file proves; this one bridges.

**Nothing here is new mathematics.** All six were proved earlier inside `CH2.v1`'s solution, where
a ladder argument needed them; the work in this node is stating them where other consumers can
reach them, and the work in this file is the six-line bridge.

The only shape difference is the usual one: a conclusion is a closed `Prop` with everything
universally quantified, while the lemmas take their arguments implicitly. So each bridge is
`fun s hs ... ↦ lemma hs ...` and nothing more.
-/

theorem ZetaZeroes.v1.challenge_no_nontrivial_zeroes_left :
    ZetaZeroes.v1.no_nontrivial_zeroes_left :=
  fun _ hs h ↦ ZetaZeroesSolution.riemannZeta_ne_zero_of_re_neg hs h

theorem ZetaZeroes.v1.challenge_zeroes_off_axis_in_strip :
    ZetaZeroes.v1.zeroes_off_axis_in_strip :=
  fun _ hz him ↦ ZetaZeroesSolution.re_mem_Icc_of_riemannZeta_eq_zero hz him

theorem ZetaZeroes.v1.challenge_finite_zeroes_on_compact :
    ZetaZeroes.v1.finite_zeroes_on_compact :=
  fun _ hK h1 ↦ ZetaZeroesSolution.finite_zeros_riemannZeta_of_isCompact hK h1

theorem ZetaZeroes.v1.challenge_exists_ordinate_free_height :
    ZetaZeroes.v1.exists_ordinate_free_height :=
  fun _ hT₀ ↦ ZetaZeroesSolution.exists_ordinate_free_height hT₀

theorem ZetaZeroes.v1.challenge_zeta_eq_zeta1_div :
    ZetaZeroes.v1.zeta_eq_zeta1_div :=
  fun _ hs ↦ ZetaZeroesSolution.riemannZeta_eq_riemannZeta₁_div hs

theorem ZetaZeroes.v1.challenge_zeta_eq_zero_iff_zeta1 :
    ZetaZeroes.v1.zeta_eq_zero_iff_zeta1 :=
  fun _ hs ↦ ZetaZeroesSolution.riemannZeta_eq_zero_iff_riemannZeta₁ hs
