/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The modulus comparison is the positive-square identity
|W*|+|W|-W-W* = (U-I)|W|(U*-I), for the explicitly constructed polar unitary.
This is a concrete matrix inequality, independent of the Furuta branch.
-/
import NLA.MI24.PolarPowers
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

lemma matrixModulus_eq_spectralPower {n : ℕ} (W : Mat n) :
    matrixModulus W = spectralPower (star W * W) (1 / 2) := by
  unfold matrixModulus CFC.abs
  exact (spectralPower_half_eq_sqrt _).symm

lemma polar_modulus_comparison {n : ℕ} (W : Mat n) (hW : IsUnit W) :
    W + star W ≤ matrixModulus (star W) + matrixModulus W := by
  obtain ⟨U, hpolar⟩ := exists_unitary_polar W hW
  let M := star W * W
  let H := spectralPower M (1 / 2)
  have hm : M.PosDef := star_mul_self_posDef W hW
  have hh : H.PosDef := spectralPower_posDef M hm _
  have hp : W = (U : Mat n) * H := hpolar
  have hmod : matrixModulus W = H := matrixModulus_eq_spectralPower W
  have hmodstar : matrixModulus (star W) = (U : Mat n) * H * star (U : Mat n) := by
    rw [matrixModulus_eq_spectralPower, star_star]
    apply spectralPower_half_unique
    · exact (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := H)
        (Unitary.isUnit_coe (U := U))).mpr hh
    · calc
        ((U : Mat n) * H * star (U : Mat n)) *
            ((U : Mat n) * H * star (U : Mat n)) =
          (U : Mat n) * H * (star (U : Mat n) * U) * H * star (U : Mat n) := by
            simp only [mul_assoc]
        _ = ((U : Mat n) * H) * (H * star (U : Mat n)) := by
          rw [Unitary.coe_star_mul_self]
          simp only [mul_one, mul_assoc]
        _ = ((U : Mat n) * H) * star ((U : Mat n) * H) := by
          rw [star_mul, hh.isHermitian.star_eq]
        _ = W * star W := by rw [← hp]
  apply sub_nonneg.mp
  rw [hmodstar, hmod, hp, star_mul, hh.isHermitian.star_eq]
  have hpos := star_right_conjugate_nonneg hh.posSemidef.nonneg ((U : Mat n) - 1)
  convert hpos using 1
  rw [star_sub, star_one]
  noncomm_ring

end NLA.MI24
