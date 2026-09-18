/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The C-star order lemmas use the genuine Euclidean operator norm instance only
in the two scoped order bridges. Their statements use the frozen concrete matrix
order and spectralPower. No default matrix norm is substituted for Schatten-infinity.
-/
import NLA.MI24.SpectralPowers
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

lemma spectralPower_comp {n : ℕ} (A : Mat n) (hA : A.PosDef) (r s : ℝ) :
    spectralPower (spectralPower A r) s = spectralPower A (r * s) := by
  by_cases hr : r = 0
  · rw [hr, spectralPower_zero A hA, zero_mul, spectralPower_zero A hA]
    exact CFC.one_rpow
  · exact CFC.rpow_rpow A r s hr hA.isStrictlyPositive

lemma spectralPower_sandwich_same {n : ℕ} (A : Mat n) (hA : A.PosDef) (r s : ℝ) :
    spectralPower A r * spectralPower A s * spectralPower A r =
      spectralPower A (2 * r + s) := by
  rw [spectralPower_mul A hA, spectralPower_mul A hA]
  congr 1
  ring

open scoped Matrix.Norms.L2Operator in
lemma spectralPower_order {n : ℕ} (A B : Mat n) (hAB : A ≤ B)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    spectralPower A r ≤ spectralPower B r := by
  exact CFC.rpow_le_rpow ⟨hr0, hr1⟩ hAB

open scoped Matrix.Norms.L2Operator in
lemma spectralPower_inverse_order {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hAB : A ≤ B) :
    spectralPower B (-1) ≤ spectralPower A (-1) := by
  exact CStarAlgebra.rpow_neg_one_le_rpow_neg_one hAB hA.isStrictlyPositive

/-- The required negative exponent interval follows from inverse antitonicity
and positive-power monotonicity; it is not an unproved extension of Loewner-Heinz. -/
lemma spectralPower_negative_order {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (hAB : A ≤ B)
    (r : ℝ) (hr0 : -1 ≤ r) (hr1 : r ≤ 0) :
    spectralPower B r ≤ spectralPower A r := by
  have h := spectralPower_order (spectralPower B (-1)) (spectralPower A (-1))
    (spectralPower_inverse_order A B hA hAB) (-r) (by linarith) (by linarith)
  rw [spectralPower_comp B hB, spectralPower_comp A hA] at h
  simpa only [neg_one_mul, neg_neg] using h

lemma hermitian_sandwich_order {n : ℕ} (A B S : Mat n)
    (hAB : A ≤ B) (hS : S.IsHermitian) : S * A * S ≤ S * B * S := by
  exact IsSelfAdjoint.conjugate_le_conjugate hAB hS.isSelfAdjoint

end NLA.MI24
