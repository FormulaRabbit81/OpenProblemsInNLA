/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The compound block and its allocation are compared after forming the same
full original word. Multiplicativity then applies the proved entry norm
identity once, with a fixed dimension factor, rather than once per letter.
The existing compact-family growth comparison removes this fixed factor from
the radius and transfers uniform product boundedness.
-/
import NLA.MF06.CompoundBlockEntries
import NLA.MF06.CompoundRadius
import NLA.MF06.AllocationPairRadius

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

def compoundDiagonalMap {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (t : Fin (Fintype.card (DegreeAllocation b k))) :
    Square d → Square (blockDim (compoundAllocationLabel b k) t) :=
  fun A => blockMatrix (compoundAllocationLabel b k) t (compoundMatrix k A)

lemma continuous_compoundDiagonalMap {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (t : Fin (Fintype.card (DegreeAllocation b k))) : Continuous (compoundDiagonalMap b k t) :=
  (continuous_blockMatrix (compoundAllocationLabel b k) t).comp (continuous_compoundMatrix k)

lemma compoundDiagonalFamily_eq {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (t : Fin (Fintype.card (DegreeAllocation b k))) (M : Set (Square d)) :
    diagonalFamily (compoundAllocationLabel b k) t (compoundFamily k M) =
      (compoundDiagonalMap b k t) '' M := by
  unfold diagonalFamily compoundFamily compoundDiagonalMap
  rw [Set.image_image]

lemma compoundFamily_upper {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (M : Set (Square d)) (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) :
    ∀ C ∈ compoundFamily k M, IsUpperBlockTriangular (compoundAllocationLabel b k) C := by
  rintro C ⟨A, hA, rfl⟩
  exact compoundMatrix_upperBlock b k A (hupper A hA)

lemma compoundDiagonal_word_actual {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (t : Fin (Fintype.card (DegreeAllocation b k))) (M : Set (Square d))
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (w : List (Square d)) (hw : WordIn M w) :
    matrixProduct (w.map (compoundDiagonalMap b k t)) =
      compoundDiagonalMap b k t (matrixProduct w) := by
  have h := blockMatrix_matrixProduct (compoundAllocationLabel b k) t
    (compoundFamily k M) (compoundFamily_upper b k M hupper)
    (w.map (compoundMatrix k)) (word_image_in M (compoundMatrix k) w hw)
  rw [compound_word_product, List.map_map] at h
  -- The composed map is the same original list, first compounded and then
  -- restricted to the fixed compound block; no independent letters appear.
  change compoundDiagonalMap b k t (matrixProduct w) =
    matrixProduct (w.map (fun A => blockMatrix (compoundAllocationLabel b k) t
      (compoundMatrix k A))) at h
  exact h.symm

lemma compoundDiagonal_word_norm_comparison {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (t : Fin (Fintype.card (DegreeAllocation b k))) (M : Set (Square d))
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (w : List (Square d)) (hw : WordIn M w) :
    spectralNorm (matrixProduct (w.map (compoundDiagonalMap b k t))) ≤
        (blockDim (compoundAllocationLabel b k) t : ℝ) *
          spectralNorm (matrixProduct (w.map (allocationMatrix b (allocationOrderEquiv b k t).val))) ∧
      spectralNorm (matrixProduct (w.map (allocationMatrix b (allocationOrderEquiv b k t).val))) ≤
        (allocationDim b (allocationOrderEquiv b k t).val : ℝ) *
          spectralNorm (matrixProduct (w.map (compoundDiagonalMap b k t))) := by
  rw [compoundDiagonal_word_actual b k t M hupper w hw,
    allocation_word_actual b M hupper (allocationOrderEquiv b k t).val w hw]
  exact compoundBlock_norm_comparison b k (matrixProduct w)
    (matrixProduct_upperBlock b M hupper w hw) t

lemma compoundDiagonal_radius_eq {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (t : Fin (Fintype.card (DegreeAllocation b k))) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) :
    jointSpectralRadius (diagonalFamily (compoundAllocationLabel b k) t (compoundFamily k M)) =
      jointSpectralRadius (allocationFamily b (allocationOrderEquiv b k t).val M) := by
  rw [compoundDiagonalFamily_eq]
  have hm := blockDim_pos_of_surjective (compoundAllocationLabel b k)
    (compoundAllocationLabel_surjective b k) t
  have hn := (allocation_dimensions b (allocationOrderEquiv b k t).val).2.2
  apply le_antisymm
  · apply image_radius_le_of_word_comparison hm hn M hM hneM
      (compoundDiagonalMap b k t) (allocationMatrix b (allocationOrderEquiv b k t).val)
      (continuous_compoundDiagonalMap b k t)
      (continuous_allocationMatrix b (allocationOrderEquiv b k t).val)
      (max 1 (blockDim (compoundAllocationLabel b k) t : ℝ)) (le_max_left _ _)
    intro w hw
    exact (compoundDiagonal_word_norm_comparison b k t M hupper w hw).1.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (spectralNorm_nonneg _))
  · apply image_radius_le_of_word_comparison hn hm M hM hneM
      (allocationMatrix b (allocationOrderEquiv b k t).val) (compoundDiagonalMap b k t)
      (continuous_allocationMatrix b (allocationOrderEquiv b k t).val)
      (continuous_compoundDiagonalMap b k t)
      (max 1 (allocationDim b (allocationOrderEquiv b k t).val : ℝ)) (le_max_left _ _)
    intro w hw
    exact (compoundDiagonal_word_norm_comparison b k t M hupper w hw).2.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (spectralNorm_nonneg _))

lemma compoundDiagonal_product_bounded {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (t : Fin (Fintype.card (DegreeAllocation b k))) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (hbounded : IsProductBounded (allocationFamily b (allocationOrderEquiv b k t).val M)) :
    IsProductBounded (diagonalFamily (compoundAllocationLabel b k) t (compoundFamily k M)) := by
  rw [compoundDiagonalFamily_eq]
  apply image_product_bounded_of_word_comparison M hM hneM
    (compoundDiagonalMap b k t) (allocationMatrix b (allocationOrderEquiv b k t).val)
    (continuous_compoundDiagonalMap b k t)
    (continuous_allocationMatrix b (allocationOrderEquiv b k t).val)
    (max 1 (blockDim (compoundAllocationLabel b k) t : ℝ)) (le_max_left _ _) ?_ hbounded
  intro w hw
  exact (compoundDiagonal_word_norm_comparison b k t M hupper w hw).1.trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (spectralNorm_nonneg _))

#print axioms compoundDiagonal_radius_eq
#assert_trust kernel compoundDiagonal_radius_eq
#print axioms compoundDiagonal_product_bounded
#assert_trust kernel compoundDiagonal_product_bounded

end NLA.MF06
