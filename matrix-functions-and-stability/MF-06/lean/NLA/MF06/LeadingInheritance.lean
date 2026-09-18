/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Actual word comparisons transfer original diagonal bounds and paired radii to
the inherited leading partition. The grouped leading/final paired radius is
then obtained from the proved tensor-block radius theorem, not assumed.
-/
import NLA.MF06.LeadingWords
import NLA.MF06.TensorBlockRadius

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma leading_diagonal_product_bounded {d r : ℕ} (b : Fin d → Fin (r + 1)) (i : Fin r)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (hb : IsProductBounded (diagonalFamily b i.castSucc M)) :
    IsProductBounded (diagonalFamily (leadingBlockLabel b) i (diagonalFamily (lastSplit b) 0 M)) := by
  have hword (w : List (Square d)) (hw : WordIn M w) :
      spectralNorm (matrixProduct (w.map (leadingBlockMap b i))) ≤
        max 1 (blockDim (leadingBlockLabel b) i : ℝ) *
          spectralNorm (matrixProduct (w.map (blockMatrix b i.castSucc))) :=
    (leadingBlock_word_norm_le b i M hupper w hw).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (spectralNorm_nonneg _))
  have hresult := image_product_bounded_of_word_comparison M hM hneM
    (leadingBlockMap b i) (blockMatrix b i.castSucc) (continuous_leadingBlockMap b i)
    (continuous_blockMatrix b i.castSucc) (max 1 (blockDim (leadingBlockLabel b) i : ℝ))
    (le_max_left _ _) hword hb
  -- leadingBlockMap is definitionally the composite of the two block maps.
  -- Expose that function before normalizing the nested set images.
  change IsProductBounded ((fun A =>
    blockMatrix (leadingBlockLabel b) i (blockMatrix (lastSplit b) 0 A)) '' M) at hresult
  simpa only [diagonalFamily, Set.image_image, Function.comp_def] using hresult

lemma final_diagonal_product_bounded {d r : ℕ} (b : Fin d → Fin (r + 1))
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (hb : IsProductBounded (diagonalFamily b (Fin.last r) M)) :
    IsProductBounded (diagonalFamily (lastSplit b) 1 M) := by
  apply image_product_bounded_of_word_comparison M hM hneM
    (blockMatrix (lastSplit b) 1) (blockMatrix b (Fin.last r))
    (continuous_blockMatrix (lastSplit b) 1) (continuous_blockMatrix b (Fin.last r))
    (max 1 (blockDim (lastSplit b) 1 : ℝ)) (le_max_left _ _) ?_ hb
  intro w hw
  exact (finalBlock_word_norm_le b M hupper w hw).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (spectralNorm_nonneg _))

lemma leading_pair_radius_le {d r : ℕ} (b : Fin d → Fin (r + 1))
    (hb : Function.Surjective b) (i j : Fin r)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) :
    jointSpectralRadius (pairedFamily (diagonalFamily (lastSplit b) 0 M)
      (blockMatrix (leadingBlockLabel b) i) (blockMatrix (leadingBlockLabel b) j)) ≤
      jointSpectralRadius (pairedFamily M (blockMatrix b i.castSucc) (blockMatrix b j.castSucc)) := by
  let H := fun A : Square d => tensorMatrix (leadingBlockMap b i A) (leadingBlockMap b j A)
  let G := fun A : Square d => tensorMatrix (blockMatrix b i.castSucc A) (blockMatrix b j.castSucc A)
  have hH : Continuous H := continuous_tensorMatrix.comp
    ((continuous_leadingBlockMap b i).prodMk (continuous_leadingBlockMap b j))
  have hG : Continuous G := continuous_tensorMatrix.comp
    ((continuous_blockMatrix b i.castSucc).prodMk (continuous_blockMatrix b j.castSucc))
  have hlead := leadingBlockLabel_surjective b hb
  have hdimH : 1 ≤ blockDim (leadingBlockLabel b) i * blockDim (leadingBlockLabel b) j :=
    one_le_mul_of_one_le_of_one_le (blockDim_pos_of_surjective _ hlead i)
      (blockDim_pos_of_surjective _ hlead j)
  have hdimG : 1 ≤ blockDim b i.castSucc * blockDim b j.castSucc :=
    one_le_mul_of_one_le_of_one_le (blockDim_pos_of_surjective b hb i.castSucc)
      (blockDim_pos_of_surjective b hb j.castSucc)
  have hD : (1 : ℝ) ≤ ((blockDim (leadingBlockLabel b) i * blockDim (leadingBlockLabel b) j : ℕ) : ℝ) :=
    by exact_mod_cast hdimH
  have hresult := image_radius_le_of_word_comparison hdimH hdimG M hM hneM H G hH hG
    ((blockDim (leadingBlockLabel b) i * blockDim (leadingBlockLabel b) j : ℕ) : ℝ) hD
      (leading_pair_word_norm_le b i j M hupper)
  simpa only [pairedFamily, diagonalFamily, Set.image_image, Function.comp_def, H, G, leadingBlockMap]
    using hresult

lemma leading_final_pair_radius_le {d r : ℕ} (hr : 1 ≤ r) (b : Fin d → Fin (r + 1))
    (hb : Function.Surjective b) (i : Fin r)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) :
    jointSpectralRadius (pairedFamily M (leadingBlockMap b i) (blockMatrix (lastSplit b) 1)) ≤
      jointSpectralRadius (pairedFamily M (blockMatrix b i.castSucc) (blockMatrix b (Fin.last r))) := by
  let H := fun A : Square d => tensorMatrix (leadingBlockMap b i A) (blockMatrix (lastSplit b) 1 A)
  let G := fun A : Square d => tensorMatrix (blockMatrix b i.castSucc A) (blockMatrix b (Fin.last r) A)
  have hH : Continuous H := continuous_tensorMatrix.comp
    ((continuous_leadingBlockMap b i).prodMk (continuous_blockMatrix (lastSplit b) 1))
  have hG : Continuous G := continuous_tensorMatrix.comp
    ((continuous_blockMatrix b i.castSucc).prodMk (continuous_blockMatrix b (Fin.last r)))
  have hdimH : 1 ≤ blockDim (leadingBlockLabel b) i * blockDim (lastSplit b) 1 :=
    one_le_mul_of_one_le_of_one_le
      (blockDim_pos_of_surjective _ (leadingBlockLabel_surjective b hb) i)
      (blockDim_pos_of_surjective _ (lastSplit_surjective hr b hb) 1)
  have hdimG : 1 ≤ blockDim b i.castSucc * blockDim b (Fin.last r) :=
    one_le_mul_of_one_le_of_one_le (blockDim_pos_of_surjective b hb i.castSucc)
      (blockDim_pos_of_surjective b hb (Fin.last r))
  have hD : (1 : ℝ) ≤ ((blockDim (leadingBlockLabel b) i * blockDim (lastSplit b) 1 : ℕ) : ℝ) :=
    by exact_mod_cast hdimH
  exact image_radius_le_of_word_comparison hdimH hdimG M hM hneM H G hH hG
    ((blockDim (leadingBlockLabel b) i * blockDim (lastSplit b) 1 : ℕ) : ℝ) hD
      (leading_final_pair_word_norm_le b i M hupper)

lemma grouped_leading_final_radius_lt {d r : ℕ} (hr : 1 ≤ r) (b : Fin d → Fin (r + 1))
    (hb : Function.Surjective b) (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (hpair : ∀ i : Fin r,
      jointSpectralRadius (pairedFamily M (blockMatrix b i.castSucc) (blockMatrix b (Fin.last r))) < 1) :
    jointSpectralRadius (pairedFamily M (blockMatrix (lastSplit b) 0) (blockMatrix (lastSplit b) 1)) < 1 := by
  have hsplit := lastSplit_surjective hr b hb
  apply paired_radius_lt_one_of_blocks
    (blockDim_pos_of_surjective _ hsplit 0) (blockDim_pos_of_surjective _ hsplit 1)
    (leadingBlockLabel b) (leadingBlockLabel_surjective b hb) M hM hneM
    (blockMatrix (lastSplit b) 0) (blockMatrix (lastSplit b) 1)
    (continuous_blockMatrix (lastSplit b) 0) (continuous_blockMatrix (lastSplit b) 1)
    (fun A hA => leadingBlockLabel_upper b A (hupper A hA))
  intro i
  exact (leading_final_pair_radius_le hr b hb i M hM hneM hupper).trans_lt (hpair i)

#print axioms leading_diagonal_product_bounded
#assert_trust kernel leading_diagonal_product_bounded
#print axioms leading_pair_radius_le
#assert_trust kernel leading_pair_radius_le
#print axioms grouped_leading_final_radius_lt
#assert_trust kernel grouped_leading_final_radius_lt

end NLA.MF06
