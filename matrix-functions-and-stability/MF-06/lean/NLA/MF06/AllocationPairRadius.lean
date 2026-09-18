/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The same full triangular word supplies all allocation products. Boundedness
of the min allocation and the exact entry-based max/min bridge dominate the
paired radius by the max-allocation radius. Singular products stay included.
-/
import NLA.MF06.AllocationProducts
import NLA.MF06.AllocationNormBridge
import NLA.MF06.ImageWordComparison
import NLA.MF06.PairedWords

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma allocation_word_actual {d r : ℕ} (b : Fin d → Fin r)
    (M : Set (Square d)) (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (a : Allocation b) (w : List (Square d)) (hw : WordIn M w) :
    matrixProduct (w.map (allocationMatrix b a)) = allocationMatrix b a (matrixProduct w) := by
  rw [allocation_word_product, allocationMatrix_eq_allocationTensor]
  congr 1
  funext i
  exact (blockMatrix_matrixProduct b i M hupper w hw).symm

lemma allocation_pair_radius_le_max {d r : ℕ} (b : Fin d → Fin r)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) (a c : Allocation b)
    (hmin : IsProductBounded (allocationFamily b (allocationMin a c) M)) :
    jointSpectralRadius (pairedFamily M (allocationMatrix b a) (allocationMatrix b c)) ≤
      jointSpectralRadius (allocationFamily b (allocationMax a c) M) := by
  obtain ⟨D, hD, hbridge⟩ := allocation_tensor_norm_bridge b a c
  obtain ⟨K, hK, hbounded⟩ := hmin
  let f := fun A : Square d => tensorMatrix (allocationMatrix b a A) (allocationMatrix b c A)
  let g := allocationMatrix b (allocationMax a c)
  have hf : Continuous f := continuous_tensorMatrix.comp
    ((continuous_allocationMatrix b a).prodMk (continuous_allocationMatrix b c))
  have hdim : 1 ≤ allocationDim b a * allocationDim b c :=
    one_le_mul_of_one_le_of_one_le (allocation_dimensions b a).2.2
      (allocation_dimensions b c).2.2
  have hword (w : List (Square d)) (hw : WordIn M w) :
      spectralNorm (matrixProduct (w.map f)) ≤
        max 1 (D * K) * spectralNorm (matrixProduct (w.map g)) := by
    have hminword : spectralNorm (allocationMatrix b (allocationMin a c) (matrixProduct w)) ≤ K := by
      rw [← allocation_word_actual b M hupper (allocationMin a c) w hw]
      exact (word_le_familyGrowth (allocationFamily b (allocationMin a c) M)
        (hM.image (continuous_allocationMatrix b (allocationMin a c))) w.length
        (w.map (allocationMatrix b (allocationMin a c))) (by simp only [List.length_map])
        (word_image_in M (allocationMatrix b (allocationMin a c)) w hw)).trans
        (hbounded w.length)
    change spectralNorm (matrixProduct (w.map (fun A =>
      tensorMatrix (allocationMatrix b a A) (allocationMatrix b c A)))) ≤ _
    rw [paired_matrixProduct, allocation_word_actual b M hupper a w hw,
      allocation_word_actual b M hupper c w hw]
    change _ ≤ max 1 (D * K) * spectralNorm
      (matrixProduct (w.map (allocationMatrix b (allocationMax a c))))
    rw [allocation_word_actual b M hupper (allocationMax a c) w hw]
    calc
      spectralNorm (tensorMatrix (allocationMatrix b a (matrixProduct w))
          (allocationMatrix b c (matrixProduct w))) ≤
          D * spectralNorm (allocationMatrix b (allocationMax a c) (matrixProduct w)) *
            spectralNorm (allocationMatrix b (allocationMin a c) (matrixProduct w)) := hbridge _
      _ ≤ D * spectralNorm (allocationMatrix b (allocationMax a c) (matrixProduct w)) * K :=
        mul_le_mul_of_nonneg_left hminword (mul_nonneg hD.le (spectralNorm_nonneg _))
      _ = (D * K) * spectralNorm (allocationMatrix b (allocationMax a c) (matrixProduct w)) := by ring
      _ ≤ max 1 (D * K) * spectralNorm (allocationMatrix b (allocationMax a c) (matrixProduct w)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (spectralNorm_nonneg _)
  exact image_radius_le_of_word_comparison hdim (allocation_dimensions b (allocationMax a c)).2.2
    M hM hneM f g hf (continuous_allocationMatrix b (allocationMax a c))
    (max 1 (D * K)) (le_max_left _ _) hword

#print axioms allocation_pair_radius_le_max
#assert_trust kernel allocation_pair_radius_le_max

end NLA.MF06
