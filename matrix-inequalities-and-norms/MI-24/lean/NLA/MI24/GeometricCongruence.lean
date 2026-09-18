/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The ordered CFC geometric mean is the unique positive definite solution
Y A^{-1} Y = B. Congruence invariance follows from this characterization;
no congruence identity for noncommuting square roots is assumed.
-/
import NLA.MI24.MeanPositivity

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

lemma half_mul_neg_half {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    spectralPower A (1 / 2) * spectralPower A (-1 / 2) = 1 := by
  convert spectralPower_mul_neg A hA (1 / 2) using 1
  norm_num

lemma neg_half_mul_half {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    spectralPower A (-1 / 2) * spectralPower A (1 / 2) = 1 := by
  convert spectralPower_neg_mul A hA (1 / 2) using 1
  norm_num

lemma neg_half_mul_self {n : ℕ} (hn : 1 ≤ n) (A : Mat n) (hA : A.PosDef) :
    spectralPower A (-1 / 2) * spectralPower A (-1 / 2) = A⁻¹ := by
  rw [spectralPower_mul A hA]
  convert spectral_power_inverse hn A hA using 1
  norm_num

lemma half_inv_half {n : ℕ} (hn : 1 ≤ n) (A : Mat n) (hA : A.PosDef) :
    spectralPower A (1 / 2) * A⁻¹ * spectralPower A (1 / 2) = 1 := by
  rw [← spectral_power_inverse hn A hA,
    spectralPower_mul A hA, spectralPower_mul A hA]
  convert spectralPower_zero A hA using 1
  norm_num

lemma geometricMean_riccati {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    geometricMean A B * A⁻¹ * geometricMean A B = B := by
  let H := spectralPower A (1 / 2)
  let F := spectralPower A (-1 / 2)
  let T := F * B * F
  let U := spectralPower T (1 / 2)
  have ht : T.PosDef := geometric_inner_posDef A B hA hB
  have hh : H * A⁻¹ * H = 1 := half_inv_half hn A hA
  have hHF : H * F = 1 := half_mul_neg_half A hA
  have hFH : F * H = 1 := neg_half_mul_half A hA
  have huu : U * U = T := spectralPower_half_mul_self T ht
  -- Expose the defining geometric-mean sandwich in the local H/U factors;
  -- the following inverse cancellations then avoid unfolding spectral powers.
  change (H * U * H) * A⁻¹ * (H * U * H) = B
  calc
    (H * U * H) * A⁻¹ * (H * U * H) =
        H * U * (H * A⁻¹ * H) * U * H := by simp only [mul_assoc]
    _ = H * (U * U) * H := by rw [hh]; simp only [mul_one, mul_assoc]
    _ = H * T * H := by rw [huu]
    _ = (H * F) * B * (F * H) := by dsimp only [T]; simp only [mul_assoc]
    _ = B := by rw [hHF, hFH]; simp

/-- The normalization by A^{-1/2} converts the Riccati equation into a positive
square-root equation. Uniqueness is Mathlib's actual CFC square-root uniqueness. -/
lemma geometricMean_eq_of_posDef_solution {n : ℕ} (hn : 1 ≤ n) (A B Y : Mat n)
    (hA : A.PosDef) (hY : Y.PosDef) (heq : Y * A⁻¹ * Y = B) :
    geometricMean A B = Y := by
  let H := spectralPower A (1 / 2)
  let F := spectralPower A (-1 / 2)
  let Z := F * Y * F
  let T := F * B * F
  have hZ : Z.PosDef := posDef_hermitian_sandwich Y F hY
    (spectralPower_isHermitian A hA _) (spectralPower_isUnit A hA _)
  have hFF : F * F = A⁻¹ := neg_half_mul_self hn A hA
  have hHF : H * F = 1 := half_mul_neg_half A hA
  have hFH : F * H = 1 := neg_half_mul_half A hA
  have hZZ : Z * Z = T := by
    -- Expand only the local Z and T abbreviations so the Riccati equation
    -- can rewrite the middle Y * A⁻¹ * Y factor after reassociation.
    change (F * Y * F) * (F * Y * F) = F * B * F
    calc
      (F * Y * F) * (F * Y * F) = F * (Y * (F * F) * Y) * F := by
        simp only [mul_assoc]
      _ = F * (Y * A⁻¹ * Y) * F := by rw [hFF]
      _ = F * B * F := by rw [heq]
  have hroot : spectralPower T (1 / 2) = Z := spectralPower_half_unique T Z hZ hZZ
  -- Expose the geometricMean wrapper as H * sqrt(T) * H so the proved
  -- square-root uniqueness equality hroot applies to the exact inner factor.
  change H * spectralPower T (1 / 2) * H = Y
  rw [hroot]
  calc
    H * Z * H = (H * F) * Y * (F * H) := by dsimp only [Z]; simp only [mul_assoc]
    _ = Y := by rw [hHF, hFH]; simp

theorem geometric_congruence {n : ℕ} (hn : 1 ≤ n) (A B S : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (hS : IsUnit S) :
    geometricMean (S * A * S.conjTranspose) (S * B * S.conjTranspose) =
      S * geometricMean A B * S.conjTranspose := by
  have hAS : (S * A * S.conjTranspose).PosDef := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := A) hS).mpr hA
  have hYS : (S * geometricMean A B * S.conjTranspose).PosDef := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := geometricMean A B) hS).mpr
        (geometricMean_posDef A B hA hB)
  apply geometricMean_eq_of_posDef_solution hn _ _ _ hAS hYS
  have hsleft : S⁻¹ * S = 1 :=
    Matrix.nonsing_inv_mul S (S.isUnit_iff_isUnit_det.mp hS)
  have hsstar : IsUnit S.conjTranspose := by
    simpa only [Matrix.star_eq_conjTranspose] using hS.star
  have hsright : S.conjTranspose * S.conjTranspose⁻¹ = 1 :=
    Matrix.mul_nonsing_inv S.conjTranspose
      (S.conjTranspose.isUnit_iff_isUnit_det.mp hsstar)
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  calc
    (S * geometricMean A B * S.conjTranspose) *
        (S.conjTranspose⁻¹ * (A⁻¹ * S⁻¹)) *
        (S * geometricMean A B * S.conjTranspose) =
      S * geometricMean A B * (S.conjTranspose * S.conjTranspose⁻¹) *
        A⁻¹ * (S⁻¹ * S) * geometricMean A B * S.conjTranspose := by
          simp only [mul_assoc]
    _ = S * (geometricMean A B * A⁻¹ * geometricMean A B) * S.conjTranspose := by
      rw [hsright, hsleft]
      simp only [mul_one, mul_assoc]
    _ = S * B * S.conjTranspose := by rw [geometricMean_riccati hn A B hA hB]

end NLA.MI24
