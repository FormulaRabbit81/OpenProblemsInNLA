/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Lin's expression is used in its original ordered form. The two polar moduli
become the geometric mean and Lin's quantity after congruence by A^(1/2).
-/
import NLA.MI24.PolarModulus
import NLA.MI24.OrderPowers

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

theorem lin_comparison {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    heronCross A B ≤ geometricMean A B + linQuantity A B := by
  let H := spectralPower A (1 / 2)
  let F := spectralPower A (-1 / 2)
  let K := spectralPower B (1 / 2)
  let W := F * K
  have hH : H.PosDef := spectralPower_posDef A hA _
  have hF : F.PosDef := spectralPower_posDef A hA _
  have hK : K.PosDef := spectralPower_posDef B hB _
  have hW : IsUnit W := hF.isUnit.mul hK.isUnit
  have hHF : H * F = 1 := half_mul_neg_half A hA
  have hFH : F * H = 1 := neg_half_mul_half A hA
  have hKK : K * K = B := spectralPower_half_mul_self B hB
  have hFF : F * F = spectralPower A (-1) := by
    rw [spectral_power_inverse hn A hA]
    exact neg_half_mul_self hn A hA
  have hstarW : star W = K * F := by
    -- Expand W = F * K so star_mul exposes the adjoints of the two
    -- Hermitian spectral-power factors.
    change star (F * K) = K * F
    rw [star_mul, hK.isHermitian.star_eq, hF.isHermitian.star_eq]
  have hWWstar : W * star W = F * B * F := by
    rw [hstarW]
    -- After hstarW, expose the remaining W factor; reassociation then
    -- isolates K * K for the square-root identity.
    change (F * K) * (K * F) = F * B * F
    calc
      (F * K) * (K * F) = F * (K * K) * F := by simp only [mul_assoc]
      _ = F * B * F := by rw [hKK]
  have hWstarW : star W * W = K * spectralPower A (-1) * K := by
    rw [hstarW]
    -- After hstarW, expose W in the reverse product; the middle F * F
    -- can then be replaced by the negative first power.
    change (K * F) * (F * K) = K * spectralPower A (-1) * K
    calc
      (K * F) * (F * K) = K * (F * F) * K := by simp only [mul_assoc]
      _ = K * spectralPower A (-1) * K := by rw [hFF]
  have hmodstar : matrixModulus (star W) = spectralPower (F * B * F) (1 / 2) := by
    rw [matrixModulus_eq_spectralPower, star_star, hWWstar]
  have hmod : matrixModulus W =
      spectralPower (K * spectralPower A (-1) * K) (1 / 2) := by
    rw [matrixModulus_eq_spectralPower, hWstarW]
  have hcross : H * (W + star W) * H = heronCross A B := by
    rw [mul_add, add_mul, hstarW]
    -- Expand the remaining W and the heronCross wrapper together;
    -- this displays the H/F inverse cancellations without unfolding powers.
    change H * (F * K) * H + H * (K * F) * H = H * K + K * H
    calc
      H * (F * K) * H + H * (K * F) * H =
          (H * F) * K * H + H * K * (F * H) := by simp only [mul_assoc]
      _ = H * K + K * H := by rw [hHF, hFH]; simp only [one_mul, mul_one]; abel
  have hmeans : H * (matrixModulus (star W) + matrixModulus W) * H =
      geometricMean A B + linQuantity A B := by
    rw [mul_add, add_mul, hmodstar, hmod]
    rfl
  have h := hermitian_sandwich_order _ _ H (polar_modulus_comparison W hW) hH.isHermitian
  rwa [hcross, hmeans] at h

end NLA.MI24
