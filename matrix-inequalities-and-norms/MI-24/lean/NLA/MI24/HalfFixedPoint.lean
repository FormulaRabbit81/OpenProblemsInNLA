/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The explicit half-power mean fixed point needs no general power-mean theorem.
Its two summands are (A+G)/2 and (B+G)/2, where G=A#B. We identify them by
their positive Riccati equations and then add the literal matrix expressions.
-/
import NLA.MI24.GeometricCongruence

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

lemma riccati_reverse {n : ℕ} (A B Y : Mat n)
    (hA : A.PosDef) (hY : Y.PosDef) (heq : Y * A⁻¹ * Y = B) :
    Y * B⁻¹ * Y = A := by
  letI := hA.isUnit.invertible
  letI := hY.isUnit.invertible
  rw [← heq, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.inv_inv_of_invertible]
  calc
    Y * (Y⁻¹ * (A * Y⁻¹)) * Y = (Y * Y⁻¹) * A * (Y⁻¹ * Y) := by
      simp only [mul_assoc]
    _ = A := by simp

lemma geometricMean_comm {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) : geometricMean A B = geometricMean B A := by
  symm
  exact geometricMean_eq_of_posDef_solution hn B A (geometricMean A B) hB
    (geometricMean_posDef A B hA hB)
    (riccati_reverse A B _ hA (geometricMean_posDef A B hA hB)
      (geometricMean_riccati hn A B hA hB))

lemma half_sum_riccati {n : ℕ} (A B G : Mat n) (hA : A.PosDef)
    (heq : G * A⁻¹ * G = B) :
    ((1 / 2 : ℂ) • (A + G)) * A⁻¹ * ((1 / 2 : ℂ) • (A + G)) =
      (1 / 4 : ℂ) • (A + B + (2 : ℂ) • G) := by
  letI := hA.isUnit.invertible
  have heq' : G * (A⁻¹ * G) = B := by simpa only [mul_assoc] using heq
  have hsum : (A + G) * A⁻¹ * (A + G) = A + B + (2 : ℂ) • G := by
    simp only [add_mul, mul_add, mul_assoc, Matrix.inv_mul_of_invertible,
      Matrix.mul_inv_of_invertible, mul_one, one_mul, heq', two_smul]
    abel
  calc
    ((1 / 2 : ℂ) • (A + G)) * A⁻¹ * ((1 / 2 : ℂ) • (A + G)) =
        (1 / 4 : ℂ) • ((A + G) * A⁻¹ * (A + G)) := by
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      norm_num
    _ = (1 / 4 : ℂ) • (A + B + (2 : ℂ) • G) := by rw [hsum]

theorem power_half_fixed_point {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    powerHalfP A B = (1 / 2 : ℂ) •
      (geometricMean (powerHalfP A B) A + geometricMean (powerHalfP A B) B) := by
  let G := geometricMean A B
  let U := (1 / 2 : ℂ) • (A + G)
  let V := (1 / 2 : ℂ) • (B + G)
  have hg : G.PosDef := geometricMean_posDef A B hA hB
  have hhalf : (0 : ℂ) < 1 / 2 := by norm_num [Complex.lt_def]
  have hu : U.PosDef := (hA.add hg).smul hhalf
  have hv : V.PosDef := (hB.add hg).smul hhalf
  have hp : (powerHalfP A B).PosDef := (matrix_means_posdef hn A B hA hB).2.2.1
  have hga : G * A⁻¹ * G = B := geometricMean_riccati hn A B hA hB
  have hgb : G * B⁻¹ * G = A := riccati_reverse A B G hA hg hga
  have hueq : U * A⁻¹ * U = powerHalfP A B := by
    exact half_sum_riccati A B G hA hga
  have hveq : V * B⁻¹ * V = powerHalfP A B := by
    -- Expand V as the half-sum while leaving the common target named;
    -- this puts the left side in the form of half_sum_riccati.
    change ((1 / 2 : ℂ) • (B + G)) * B⁻¹ * ((1 / 2 : ℂ) • (B + G)) = _
    rw [half_sum_riccati B A G hB hgb]
    simp only [powerHalfP, heronEndpoint, add_comm B A]
    rfl
  have hua : geometricMean (powerHalfP A B) A = U :=
    geometricMean_eq_of_posDef_solution hn _ A U hp hu
      (riccati_reverse A _ U hA hu hueq)
  have hvb : geometricMean (powerHalfP A B) B = V :=
    geometricMean_eq_of_posDef_solution hn _ B V hp hv
      (riccati_reverse B _ V hB hv hveq)
  rw [hua, hvb]
  -- Unfold the endpoint and local half-sum wrappers at this final equality;
  -- only scalar distribution and additive cancellation remain.
  change (1 / 4 : ℂ) • (A + B + (2 : ℂ) • G) =
    (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (A + G) + (1 / 2 : ℂ) • (B + G))
  simp only [smul_add, smul_smul]
  norm_num
  -- Split the complex half into two quarters so add_smul matches the
  -- two already normalized half-sum contributions.
  rw [show (1 / 2 : ℂ) = (1 / 4 : ℂ) + 1 / 4 by norm_num, add_smul]
  abel

end NLA.MI24
