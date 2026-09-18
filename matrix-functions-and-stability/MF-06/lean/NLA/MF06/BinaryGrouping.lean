/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Grouping arbitrary labeled coordinates into two fibers is an actual bijection.
For an upper binary partition its reindexed matrix is the literal two-block
matrix. Thus the two-block estimate applies without assuming that a fiber is
already an interval of the original coordinate order.
-/
import NLA.MF06.BlockAlgebra
import NLA.MF06.TwoBlockBounded
import NLA.MF06.ImageWordComparison

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

/-- The two frozen fiber enumerations together enumerate all original coordinates. -/
def binaryCoordinateEquiv {d : ℕ} (b : Fin d → Fin 2) :
    Fin (blockDim b 0) ⊕ Fin (blockDim b 1) ≃ Fin d :=
  Equiv.ofBijective (Sum.elim (blockCoordinate b 0) (blockCoordinate b 1)) (by
    constructor
    · rintro (i | i) (j | j) hij
      · exact congrArg Sum.inl ((blockCoordinate_injective b 0) hij)
      · have hbad := congrArg b hij
        simp only [Sum.elim_inl, Sum.elim_inr, blockCoordinate_label] at hbad
        norm_num at hbad
      · have hbad := congrArg b hij
        simp only [Sum.elim_inl, Sum.elim_inr, blockCoordinate_label] at hbad
        norm_num at hbad
      · exact congrArg Sum.inr ((blockCoordinate_injective b 1) hij)
    · intro j
      have hj : b j = 0 ∨ b j = 1 := by omega
      rcases hj with hj | hj
      · obtain ⟨i, hi⟩ := blockCoordinate_covers b 0 j hj
        exact ⟨Sum.inl i, hi⟩
      · obtain ⟨i, hi⟩ := blockCoordinate_covers b 1 j hj
        exact ⟨Sum.inr i, hi⟩)

def binaryReindex {d : ℕ} (b : Fin d → Fin 2) :
    Fin (blockDim b 0 + blockDim b 1) ≃ Fin d :=
  (finSumFinEquiv (m := blockDim b 0) (n := blockDim b 1)).symm.trans
    (binaryCoordinateEquiv b)

def binaryCrossMatrix {d : ℕ} (b : Fin d → Fin 2) (A : Square d) :
    Matrix (Fin (blockDim b 0)) (Fin (blockDim b 1)) ℂ :=
  A.submatrix (blockCoordinate b 0) (blockCoordinate b 1)

lemma binary_grouped_eq {d : ℕ} (b : Fin d → Fin 2) (A : Square d)
    (hA : IsUpperBlockTriangular b A) :
    A.submatrix (binaryReindex b) (binaryReindex b) =
      twoBlockMatrix (blockMatrix b 0 A) (binaryCrossMatrix b A) (blockMatrix b 1 A) := by
  ext u v
  change A (binaryCoordinateEquiv b ((finSumFinEquiv).symm u))
      (binaryCoordinateEquiv b ((finSumFinEquiv).symm v)) =
    Matrix.fromBlocks (blockMatrix b 0 A) (binaryCrossMatrix b A) 0 (blockMatrix b 1 A)
      ((finSumFinEquiv).symm u) ((finSumFinEquiv).symm v)
  cases (finSumFinEquiv (m := blockDim b 0) (n := blockDim b 1)).symm u with
  | inl i =>
      cases (finSumFinEquiv (m := blockDim b 0) (n := blockDim b 1)).symm v with
      | inl j => rfl
      | inr j => rfl
  | inr i =>
      cases (finSumFinEquiv (m := blockDim b 0) (n := blockDim b 1)).symm v with
      | inl j =>
          change A (blockCoordinate b 1 i) (blockCoordinate b 0 j) = 0
          apply hA
          simp only [blockCoordinate_label]
          decide
      | inr j => rfl

lemma spectralNorm_le_reindexed {m n : ℕ} (e : Fin m ≃ Fin n) (A : Square n) :
    spectralNorm A ≤ (n : ℝ) * spectralNorm (A.submatrix e e) := by
  have h := spectralNorm_submatrix_le (A.submatrix e e) e.symm
  simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] using h

/-- Nonresonance for an arbitrary binary partition of the original coordinates. -/
lemma binary_partition_product_bounded {d : ℕ} (b : Fin d → Fin 2)
    (hb : Function.Surjective b) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (hfirst : IsProductBounded (diagonalFamily b 0 M))
    (hsecond : IsProductBounded (diagonalFamily b 1 M))
    (hpair : jointSpectralRadius (pairedFamily M (blockMatrix b 0) (blockMatrix b 1)) < 1) :
    IsProductBounded M := by
  let H : Square d → Square (blockDim b 0 + blockDim b 1) := fun A =>
    twoBlockMatrix (blockMatrix b 0 A) (binaryCrossMatrix b A) (blockMatrix b 1 A)
  have hcross : Continuous (binaryCrossMatrix b) := continuous_id.matrix_submatrix _ _
  have hH : Continuous H := continuous_twoBlock_family _ _ _
    (continuous_blockMatrix b 0) (continuous_blockMatrix b 1) hcross
  have hbound : IsProductBounded (H '' M) := twoBlock_product_bounded
    (blockDim_pos_of_surjective b hb 0) (blockDim_pos_of_surjective b hb 1)
    M hM hneM (blockMatrix b 0) (blockMatrix b 1) (binaryCrossMatrix b)
    (continuous_blockMatrix b 0) (continuous_blockMatrix b 1) hcross hfirst hsecond hpair
  have hword (w : List (Square d)) (hw : WordIn M w) :
      spectralNorm (matrixProduct (w.map id)) ≤
        max 1 (d : ℝ) * spectralNorm (matrixProduct (w.map H)) := by
    have hmap : w.map H = w.map (fun A => A.submatrix (binaryReindex b) (binaryReindex b)) := by
      apply List.map_congr_left
      intro A hA
      exact (binary_grouped_eq b A (hupper A (hw A hA))).symm
    rw [List.map_id, hmap, matrixProduct_submatrix_equiv]
    exact (spectralNorm_le_reindexed (binaryReindex b) (matrixProduct w)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (spectralNorm_nonneg _))
  have hresult := image_product_bounded_of_word_comparison M hM hneM id H continuous_id hH
    (max 1 (d : ℝ)) (le_max_left _ _) hword hbound
  simpa only [Set.image_id] using hresult

#print axioms binary_partition_product_bounded
#assert_trust kernel binary_partition_product_bounded

end NLA.MF06
