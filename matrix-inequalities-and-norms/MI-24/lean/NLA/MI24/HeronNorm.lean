/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Scaling upgrades the order implication to the true Euclidean operator norm.
Its denominator is positive because the target is positive definite in positive
dimension. This norm comparison alone is not claimed to prove the trace contract.
-/
import NLA.MI24.HeronOrder
import NLA.MI24.OperatorNorm

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI24

lemma infinitySchattenNorm_pos {n : ℕ} (hn : 1 ≤ n) (A : Mat n)
    (hA : A.PosDef) : 0 < infinitySchattenNorm A := by
  let : NeZero n := ⟨by omega⟩
  rw [infinitySchattenNorm_eq_l2]
  exact norm_pos_iff.mpr hA.isUnit.ne_zero

lemma infinitySchattenNorm_smul_pos {n : ℕ} (A : Mat n)
    (c : ℝ) (hc : 0 < c) :
    infinitySchattenNorm ((c : ℂ) • A) = c * infinitySchattenNorm A := by
  simp only [infinitySchattenNorm_eq_l2, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hc]

lemma weightedHeronSource_norm_le {n : ℕ} (hn : 1 ≤ n) (P D : Mat n)
    (hP : P.PosDef) (hD : D.PosDef) (p : ℝ) (hp : 1 ≤ p) :
    infinitySchattenNorm (weightedHeronSource P D p) ≤
      infinitySchattenNorm (weightedHeronTarget P D p) := by
  let c := infinitySchattenNorm (weightedHeronTarget P D p)
  have hc : 0 < c := infinitySchattenNorm_pos hn _
    (weightedHeronTarget_posDef P D hP hD p)
  have hci : 0 < c⁻¹ := inv_pos.mpr hc
  let D' := ((c⁻¹ : ℝ) : ℂ) ^ 2 • D
  have hD' : D'.PosDef := hD.smul (by
    exact_mod_cast sq_pos_of_pos hci)
  have hTnorm : infinitySchattenNorm (weightedHeronTarget P D' p) = 1 := by
    dsimp only [D']
    rw [weightedHeronTarget_smul_sq P D hD p (c⁻¹) hci,
      infinitySchattenNorm_smul_pos _ (c⁻¹) hci]
    exact inv_mul_cancel₀ (ne_of_gt hc)
  have hT : weightedHeronTarget P D' p ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (weightedHeronTarget_posDef P D' hP hD' p).posSemidef.nonneg).mp
    rw [← infinitySchattenNorm_eq_l2, hTnorm]
  have hS : weightedHeronSource P D' p ≤ 1 :=
    weightedHeronSource_le_one hn P D' hP hD' p hp hT
  have hSnorm : infinitySchattenNorm (weightedHeronSource P D' p) ≤ 1 := by
    rw [infinitySchattenNorm_eq_l2]
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (weightedHeronSource_posDef P D' hP hD' p).posSemidef.nonneg).mpr hS
  dsimp only [D'] at hSnorm
  rw [weightedHeronSource_smul_sq P D hP hD p (c⁻¹) hci,
    infinitySchattenNorm_smul_pos _ (c⁻¹) hci] at hSnorm
  -- Fold the target norm into the local positive scalar c; this makes
  -- the goal identical to the scaled inequality obtained from hSnorm.
  change infinitySchattenNorm (weightedHeronSource P D p) ≤ c
  have hmul := mul_le_mul_of_nonneg_left hSnorm hc.le
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul, mul_one] using hmul

end NLA.MI24
