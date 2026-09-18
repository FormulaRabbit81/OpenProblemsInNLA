/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The complete original MI-24 comparison follows by convexity: its middle matrix
is the average of the Heron endpoint and the requested right endpoint. The
proved Heron and Lin inequalities first bound the Heron norm by the middle norm.
The triangle inequality for the actual Schatten/Euclidean norms then cancels
that middle norm. All complex positive definite pairs and all finite p >= 1,
as well as the infinity endpoint, remain in the final unchanged statement.
-/
import NLA.MI24.HeronFinite
import NLA.MI24.HeronInfinity
import NLA.MI24.PositiveSchatten
import NLA.MI24.LinComparison

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI24

lemma middleMatrix_half_sum {n : ℕ} (A B : Mat n) :
    middleMatrix A B = (1 / 2 : ℂ) • (heronEndpoint A B + rightMatrix A B) := by
  have hhalf (Z : Mat n) : (1 / 2 : ℂ) • Z + (1 / 2 : ℂ) • Z = Z := by
    rw [← add_smul]
    norm_num
  unfold middleMatrix heronEndpoint rightMatrix
  symm
  calc
    _ = ((1 / 2 : ℂ) • A + (1 / 2 : ℂ) • A) +
        ((1 / 2 : ℂ) • B + (1 / 2 : ℂ) • B) + geometricMean A B + linQuantity A B := by
      simp only [smul_add, smul_smul]
      norm_num
      abel
    _ = _ := by rw [hhalf A, hhalf B]

lemma heronCross_sum_le_middle {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) : A + B + heronCross A B ≤ middleMatrix A B := by
  simpa only [middleMatrix, add_assoc, add_comm, add_left_comm] using
    add_le_add_left (lin_comparison hn A B hA hB) (A + B)

theorem schatten_complement_finite {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (p : ℝ) (hp : 1 ≤ p) :
    finiteSchattenNorm p (middleMatrix A B) ≤
      finiteSchattenNorm p (rightMatrix A B) := by
  have hmeans := matrix_means_posdef hn A B hA hB
  have hE := hmeans.2.2.2.2.1
  have hC := hmeans.2.2.2.2.2.1
  have hM := hmeans.2.2.2.2.2.2.1
  have hR := hmeans.2.2.2.2.2.2.2
  have hleft : finiteSchattenNorm p (heronEndpoint A B) ≤
      finiteSchattenNorm p (middleMatrix A B) :=
    (heron_comparison_finite hn A B hA hB p hp).trans
      (positive_schatten_monotone hn _ _ hC.posSemidef hM.posSemidef
        (heronCross_sum_le_middle hn A B hA hB) p hp)
  have hconvex : finiteSchattenNorm p (middleMatrix A B) ≤ (1 / 2 : ℝ) *
      (finiteSchattenNorm p (heronEndpoint A B) + finiteSchattenNorm p (rightMatrix A B)) := by
    calc
      _ = finiteSchattenNorm p ((1 / 2 : ℂ) • (heronEndpoint A B + rightMatrix A B)) :=
        congrArg (finiteSchattenNorm p) (middleMatrix_half_sum A B)
      _ = (1 / 2 : ℝ) * finiteSchattenNorm p (heronEndpoint A B + rightMatrix A B) := by
        -- Rewrite the complex half as the cast of a real half, because
        -- positive_schatten_smul takes a real nonnegative scaling parameter.
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
          positive_schatten_smul hn _ (hE.posSemidef.add hR.posSemidef) p hp
            (1 / 2) (by norm_num)]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (positive_schatten_triangle hn _ _ hE.posSemidef hR.posSemidef p hp) (by norm_num)
  linarith

lemma infinitySchattenNorm_add_le {n : ℕ} (U V : Mat n) :
    infinitySchattenNorm (U + V) ≤ infinitySchattenNorm U + infinitySchattenNorm V := by
  simp only [infinitySchattenNorm_eq_l2]
  exact norm_add_le U V

theorem schatten_complement_infinity {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    infinitySchattenNorm (middleMatrix A B) ≤
      infinitySchattenNorm (rightMatrix A B) := by
  have hmeans := matrix_means_posdef hn A B hA hB
  have hC := hmeans.2.2.2.2.2.1
  have hM := hmeans.2.2.2.2.2.2.1
  have hleft : infinitySchattenNorm (heronEndpoint A B) ≤
      infinitySchattenNorm (middleMatrix A B) :=
    (heron_comparison_infinity hn A B hA hB).trans
      (positive_infinity_monotone hn _ _ hC.posSemidef hM.posSemidef
        (heronCross_sum_le_middle hn A B hA hB))
  have hconvex : infinitySchattenNorm (middleMatrix A B) ≤ (1 / 2 : ℝ) *
      (infinitySchattenNorm (heronEndpoint A B) + infinitySchattenNorm (rightMatrix A B)) := by
    calc
      _ = infinitySchattenNorm ((1 / 2 : ℂ) • (heronEndpoint A B + rightMatrix A B)) :=
        congrArg infinitySchattenNorm (middleMatrix_half_sum A B)
      _ = (1 / 2 : ℝ) * infinitySchattenNorm (heronEndpoint A B + rightMatrix A B) := by
        -- Rewrite the complex half as a real cast for the operator-norm
        -- homogeneity theorem infinitySchattenNorm_smul_pos.
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
          infinitySchattenNorm_smul_pos _ (1 / 2) (by norm_num)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (infinitySchattenNorm_add_le _ _) (by norm_num)
  linarith

theorem schattenComplementConjecture : SchattenComplementConjecture := by
  unfold SchattenComplementConjecture
  constructor
  · intro n hn A B hA hB p hp
    exact schatten_complement_finite hn A B hA hB p hp
  · intro n hn A B hA hB
    exact schatten_complement_infinity hn A B hA hB

end NLA.MI24
