/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Both paired blocks use the same original word. Entry norm correspondence in
each factor gives a literal tensor-entry norm correspondence and a fixed
source-dimension operator bound. Thus strict paired allocation radius bounds
transfer to the actual compound diagonal blocks, without any independent
choice of a matrix or word in the two factors.
-/
import NLA.MF06.CompoundAllocationWords

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma spectralNorm_tensor_le_of_entry_norm {m n p q : ℕ}
    (X : Square m) (Y : Square n) (A : Square p) (B : Square q)
    (e : Fin m → Fin p) (f : Fin n → Fin q)
    (hX : ∀ i j, ‖X i j‖ = ‖A (e i) (e j)‖)
    (hY : ∀ i j, ‖Y i j‖ = ‖B (f i) (f j)‖) :
    spectralNorm (tensorMatrix X Y) ≤ ((m * n : ℕ) : ℝ) * spectralNorm (tensorMatrix A B) := by
  apply spectralNorm_le_card_mul_entry_bound _ _ (spectralNorm_nonneg _)
  intro i j
  change ‖X ((finProdFinEquiv (m := m) (n := n)).symm i).1
        ((finProdFinEquiv (m := m) (n := n)).symm j).1 *
      Y ((finProdFinEquiv (m := m) (n := n)).symm i).2
        ((finProdFinEquiv (m := m) (n := n)).symm j).2‖ ≤ _
  rw [norm_mul, hX, hY]
  simpa only [tensorMatrix, Matrix.kronecker, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.symm_apply_apply, norm_mul] using
    spectralNorm_entry_bound (tensorMatrix A B)
      (finProdFinEquiv (e ((finProdFinEquiv (m := m) (n := n)).symm i).1,
        f ((finProdFinEquiv (m := m) (n := n)).symm i).2))
      (finProdFinEquiv (e ((finProdFinEquiv (m := m) (n := n)).symm j).1,
        f ((finProdFinEquiv (m := m) (n := n)).symm j).2))

lemma compoundDiagonal_pair_word_bound {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (s t : Fin (Fintype.card (DegreeAllocation b k))) (M : Set (Square d))
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (w : List (Square d)) (hw : WordIn M w) :
    spectralNorm (matrixProduct (w.map (fun A =>
        tensorMatrix (compoundDiagonalMap b k s A) (compoundDiagonalMap b k t A)))) ≤
      ((blockDim (compoundAllocationLabel b k) s *
        blockDim (compoundAllocationLabel b k) t : ℕ) : ℝ) *
      spectralNorm (matrixProduct (w.map (fun A =>
        tensorMatrix (allocationMatrix b (allocationOrderEquiv b k s).val A)
          (allocationMatrix b (allocationOrderEquiv b k t).val A)))) := by
  rw [paired_matrixProduct, compoundDiagonal_word_actual b k s M hupper w hw,
    compoundDiagonal_word_actual b k t M hupper w hw,
    paired_matrixProduct, allocation_word_actual b M hupper (allocationOrderEquiv b k s).val w hw,
    allocation_word_actual b M hupper (allocationOrderEquiv b k t).val w hw]
  exact spectralNorm_tensor_le_of_entry_norm _ _ _ _
    (compoundBlockAllocationEquiv b k s) (compoundBlockAllocationEquiv b k t)
    (norm_compoundBlock_entry b k (matrixProduct w) (matrixProduct_upperBlock b M hupper w hw) s)
    (norm_compoundBlock_entry b k (matrixProduct w) (matrixProduct_upperBlock b M hupper w hw) t)

lemma compoundDiagonal_pair_radius_le {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (s t : Fin (Fintype.card (DegreeAllocation b k))) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) :
    jointSpectralRadius (pairedFamily (compoundFamily k M)
      (blockMatrix (compoundAllocationLabel b k) s) (blockMatrix (compoundAllocationLabel b k) t)) ≤
      jointSpectralRadius (pairedFamily M (allocationMatrix b (allocationOrderEquiv b k s).val)
        (allocationMatrix b (allocationOrderEquiv b k t).val)) := by
  let f := fun A : Square d =>
    tensorMatrix (compoundDiagonalMap b k s A) (compoundDiagonalMap b k t A)
  let g := fun A : Square d =>
    tensorMatrix (allocationMatrix b (allocationOrderEquiv b k s).val A)
      (allocationMatrix b (allocationOrderEquiv b k t).val A)
  have hsource : pairedFamily (compoundFamily k M)
      (blockMatrix (compoundAllocationLabel b k) s) (blockMatrix (compoundAllocationLabel b k) t) =
      f '' M := by
    unfold pairedFamily compoundFamily
    rw [Set.image_image]
    rfl
  have hf : Continuous f := continuous_tensorMatrix.comp
    ((continuous_compoundDiagonalMap b k s).prodMk (continuous_compoundDiagonalMap b k t))
  have hg : Continuous g := continuous_tensorMatrix.comp
    ((continuous_allocationMatrix b (allocationOrderEquiv b k s).val).prodMk
      (continuous_allocationMatrix b (allocationOrderEquiv b k t).val))
  have hm : 1 ≤ blockDim (compoundAllocationLabel b k) s *
      blockDim (compoundAllocationLabel b k) t :=
    one_le_mul_of_one_le_of_one_le
      (blockDim_pos_of_surjective _ (compoundAllocationLabel_surjective b k) s)
      (blockDim_pos_of_surjective _ (compoundAllocationLabel_surjective b k) t)
  have hn : 1 ≤ allocationDim b (allocationOrderEquiv b k s).val *
      allocationDim b (allocationOrderEquiv b k t).val :=
    one_le_mul_of_one_le_of_one_le (allocation_dimensions b (allocationOrderEquiv b k s).val).2.2
      (allocation_dimensions b (allocationOrderEquiv b k t).val).2.2
  rw [hsource]
  apply image_radius_le_of_word_comparison hm hn M hM hneM f g hf hg
    (max 1 ((blockDim (compoundAllocationLabel b k) s *
      blockDim (compoundAllocationLabel b k) t : ℕ) : ℝ)) (le_max_left _ _)
  intro w hw
  exact (compoundDiagonal_pair_word_bound b k s t M hupper w hw).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (spectralNorm_nonneg _))

#print axioms spectralNorm_tensor_le_of_entry_norm
#assert_trust kernel spectralNorm_tensor_le_of_entry_norm
#print axioms compoundDiagonal_pair_radius_le
#assert_trust kernel compoundDiagonal_pair_radius_le

end NLA.MF06
