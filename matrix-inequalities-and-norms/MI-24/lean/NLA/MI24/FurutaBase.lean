/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

This implements the first range of Fujii's proof of Furuta's inequality
(Ann. Funct. Anal. 1(2), 2010, Lemma 1.2 and Theorem 1.3). The power-conjugation
identity is proved in PolarPowers; negative-exponent order reversal is proved
in OrderPowers. No cited theorem is inserted as a premise or axiom.
-/
import NLA.MI24.PolarPowers
import NLA.MI24.OrderPowers

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

lemma spectralPower_half_exponent_square {n : ℕ} (A : Mat n) (hA : A.PosDef)
    (r : ℝ) :
    spectralPower A (r / 2) * spectralPower A (r / 2) = spectralPower A r := by
  rw [spectralPower_mul A hA]
  congr 1
  ring

/-- Furuta's base range: the sandwich parameter t lies in [0,1], while the
positive power s may be any real number at least one. -/
lemma furuta_base {n : ℕ} (A B : Mat n) (hA : A.PosDef) (hB : B.PosDef)
    (hBA : B ≤ A) (s t : ℝ) (hs : 1 ≤ s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    spectralPower
      (spectralPower A (t / 2) * spectralPower B s * spectralPower A (t / 2))
      ((1 + t) / (s + t)) ≤ spectralPower A (1 + t) := by
  let H := spectralPower A (t / 2)
  let K := spectralPower B (s / 2)
  let W := H * K
  let D := H * spectralPower B s * H
  let E := K * spectralPower A t * K
  let a := (1 + t) / (s + t)
  let b := (1 - s) / (s + t)
  have hden : 0 < s + t := by linarith
  have hdenne : s + t ≠ 0 := ne_of_gt hden
  have ha : a - 1 = b := by
    dsimp only [a, b]
    field_simp [hdenne]
    ring
  have hb0 : -1 ≤ b := by
    dsimp only [b]
    apply (le_div_iff₀ hden).mpr
    linarith
  have hb1 : b ≤ 0 := by
    dsimp only [b]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
  have hH : H.PosDef := spectralPower_posDef A hA _
  have hK : K.PosDef := spectralPower_posDef B hB _
  have hW : IsUnit W := hH.isUnit.mul hK.isUnit
  have hE : E.PosDef := posDef_hermitian_sandwich _ K
    (spectralPower_posDef A hA _) hK.isHermitian hK.isUnit
  have hWW : W * star W = D := by
    -- Expose W = H * K and the defining sandwich D; star_mul can then
    -- reduce the adjoint and the B half-powers can be combined.
    change (H * K) * star (H * K) = H * spectralPower B s * H
    rw [star_mul, hK.isHermitian.star_eq, hH.isHermitian.star_eq]
    calc
      (H * K) * (K * H) = H * (K * K) * H := by simp only [mul_assoc]
      _ = H * spectralPower B s * H := by
        rw [spectralPower_half_exponent_square B hB s]
  have hWstarW : star W * W = E := by
    -- Expose W and E in the opposite product order; the middle H * H
    -- is then the exact factor covered by the A half-power identity.
    change star (H * K) * (H * K) = K * spectralPower A t * K
    rw [star_mul, hK.isHermitian.star_eq, hH.isHermitian.star_eq]
    calc
      (K * H) * (H * K) = K * (H * H) * K := by simp only [mul_assoc]
      _ = K * spectralPower A t * K := by
        rw [spectralPower_half_exponent_square A hA t]
  have hEt : spectralPower B (s + t) ≤ E := by
    calc
      spectralPower B (s + t) = K * spectralPower B t * K := by
        dsimp only [K]
        rw [spectralPower_sandwich_same B hB]
        congr 1
        ring
      _ ≤ K * spectralPower A t * K := hermitian_sandwich_order _ _ K
        (spectralPower_order B A hBA t ht0 ht1) hK.isHermitian
      _ = E := rfl
  have hnegative : spectralPower E b ≤ spectralPower B (1 - s) := by
    have h := spectralPower_negative_order (spectralPower B (s + t)) E
      (spectralPower_posDef B hB _) hE hEt b hb0 hb1
    rw [spectralPower_comp B hB] at h
    have hexp : (s + t) * b = 1 - s := by
      dsimp only [b]
      field_simp [hdenne]
    rwa [hexp] at h
  have hconjugate : spectralPower D a = W * spectralPower E b * star W := by
    rw [← hWW, spectralPower_mul_star_conjugation W hW a, hWstarW, ha]
  have hcollapse : W * spectralPower B (1 - s) * star W = H * B * H := by
    -- Expand W alone, retaining H and K as factors, so adjoint reduction
    -- and reassociation isolate the three powers of B.
    change (H * K) * spectralPower B (1 - s) * star (H * K) = H * B * H
    rw [star_mul, hK.isHermitian.star_eq, hH.isHermitian.star_eq]
    calc
      (H * K) * spectralPower B (1 - s) * (K * H) =
          H * (K * spectralPower B (1 - s) * K) * H := by simp only [mul_assoc]
      _ = H * spectralPower B (2 * (s / 2) + (1 - s)) * H := by
        rw [spectralPower_sandwich_same B hB]
      _ = H * B * H := by
        -- Normalize the real exponent sum to 1 before spectralPower_one; this
        -- is ring arithmetic, not a definitional equality of the written exponents.
        rw [show (2 * (s / 2) + (1 - s) : ℝ) = 1 by ring,
          spectralPower_one B hB]
  -- Fold the literal source sandwich and exponent into the local D/a
  -- abbreviations used by hconjugate and the subsequent order comparison.
  change spectralPower D a ≤ spectralPower A (1 + t)
  calc
    spectralPower D a = W * spectralPower E b * star W := hconjugate
    _ ≤ W * spectralPower B (1 - s) * star W :=
      star_right_conjugate_le_conjugate hnegative W
    _ = H * B * H := hcollapse
    _ ≤ H * A * H := hermitian_sandwich_order B A H hBA hH.isHermitian
    _ = H * spectralPower A 1 * H := by rw [spectralPower_one A hA]
    _ = spectralPower A (2 * (t / 2) + 1) := spectralPower_sandwich_same A hA _ _
    _ = spectralPower A (1 + t) := by congr 1; ring

end NLA.MI24
