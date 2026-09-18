/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Nested leading blocks and the final grouped block are literal submatrices of
the corresponding original diagonal word. The same statement is proved for
paired tensor words. The original word is preserved at every step.
-/
import NLA.MF06.LeadingPartition
import NLA.MF06.FiberCompression
import NLA.MF06.PairedWords

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

def leadingBlockMap {d r : ℕ} (b : Fin d → Fin (r + 1)) (i : Fin r)
    (A : Square d) : Square (blockDim (leadingBlockLabel b) i) :=
  blockMatrix (leadingBlockLabel b) i (blockMatrix (lastSplit b) 0 A)

def leadingFiberCoordinate {d r : ℕ} (b : Fin d → Fin (r + 1)) (i : Fin r) :
    Fin (blockDim (leadingBlockLabel b) i) → Fin (blockDim b i.castSucc) :=
  fiberCoordinate b i.castSucc
    (fun u => blockCoordinate (lastSplit b) 0 (blockCoordinate (leadingBlockLabel b) i u))
    (leading_nested_coordinate_label b i)

def finalFiberCoordinate {d r : ℕ} (b : Fin d → Fin (r + 1)) :
    Fin (blockDim (lastSplit b) 1) → Fin (blockDim b (Fin.last r)) :=
  fiberCoordinate b (Fin.last r) (blockCoordinate (lastSplit b) 1) (final_coordinate_label b)

lemma continuous_leadingBlockMap {d r : ℕ} (b : Fin d → Fin (r + 1)) (i : Fin r) :
    Continuous (leadingBlockMap b i) :=
  (continuous_blockMatrix (leadingBlockLabel b) i).comp (continuous_blockMatrix (lastSplit b) 0)

lemma leadingBlockMap_submatrix {d r : ℕ} (b : Fin d → Fin (r + 1)) (i : Fin r)
    (A : Square d) :
    leadingBlockMap b i A = (blockMatrix b i.castSucc A).submatrix
      (leadingFiberCoordinate b i) (leadingFiberCoordinate b i) :=
  submatrix_eq_block_submatrix b i.castSucc _ (leading_nested_coordinate_label b i) A

lemma finalBlock_submatrix {d r : ℕ} (b : Fin d → Fin (r + 1)) (A : Square d) :
    blockMatrix (lastSplit b) 1 A = (blockMatrix b (Fin.last r) A).submatrix
      (finalFiberCoordinate b) (finalFiberCoordinate b) :=
  submatrix_eq_block_submatrix b (Fin.last r) _ (final_coordinate_label b) A

lemma leadingBlock_word_submatrix {d r : ℕ} (b : Fin d → Fin (r + 1)) (i : Fin r)
    (M : Set (Square d)) (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (w : List (Square d)) (hw : WordIn M w) :
    matrixProduct (w.map (leadingBlockMap b i)) =
      (matrixProduct (w.map (blockMatrix b i.castSucc))).submatrix
        (leadingFiberCoordinate b i) (leadingFiberCoordinate b i) := by
  have hsplit : ∀ A ∈ M, IsUpperBlockTriangular (lastSplit b) A :=
    fun A hA => lastSplit_upper b A (hupper A hA)
  have hlead : ∀ A ∈ diagonalFamily (lastSplit b) 0 M,
      IsUpperBlockTriangular (leadingBlockLabel b) A := by
    rintro A ⟨B, hB, rfl⟩
    exact leadingBlockLabel_upper b B (hupper B hB)
  have hfirst := blockMatrix_matrixProduct (lastSplit b) 0 M hsplit w hw
  have hsecond := blockMatrix_matrixProduct (leadingBlockLabel b) i
    (diagonalFamily (lastSplit b) 0 M) hlead (w.map (blockMatrix (lastSplit b) 0))
      (word_image_in M (blockMatrix (lastSplit b) 0) w hw)
  calc
    matrixProduct (w.map (leadingBlockMap b i)) =
        blockMatrix (leadingBlockLabel b) i (matrixProduct (w.map (blockMatrix (lastSplit b) 0))) := by
      -- Expanding the map name preserves the same original chronological list w.
      change matrixProduct (w.map (fun A =>
        blockMatrix (leadingBlockLabel b) i (blockMatrix (lastSplit b) 0 A))) = _
      simpa only [List.map_map, Function.comp_def] using hsecond.symm
    _ = leadingBlockMap b i (matrixProduct w) :=
      congrArg (blockMatrix (leadingBlockLabel b) i) hfirst.symm
    _ = (blockMatrix b i.castSucc (matrixProduct w)).submatrix
        (leadingFiberCoordinate b i) (leadingFiberCoordinate b i) := leadingBlockMap_submatrix b i _
    _ = _ := by rw [blockMatrix_matrixProduct b i.castSucc M hupper w hw]

lemma finalBlock_word_submatrix {d r : ℕ} (b : Fin d → Fin (r + 1))
    (M : Set (Square d)) (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (w : List (Square d)) (hw : WordIn M w) :
    matrixProduct (w.map (blockMatrix (lastSplit b) 1)) =
      (matrixProduct (w.map (blockMatrix b (Fin.last r)))).submatrix
        (finalFiberCoordinate b) (finalFiberCoordinate b) := by
  rw [← blockMatrix_matrixProduct (lastSplit b) 1 M
    (fun A hA => lastSplit_upper b A (hupper A hA)) w hw,
    finalBlock_submatrix, blockMatrix_matrixProduct b (Fin.last r) M hupper w hw]

lemma leadingBlock_word_norm_le {d r : ℕ} (b : Fin d → Fin (r + 1)) (i : Fin r)
    (M : Set (Square d)) (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (w : List (Square d)) (hw : WordIn M w) :
    spectralNorm (matrixProduct (w.map (leadingBlockMap b i))) ≤
      (blockDim (leadingBlockLabel b) i : ℝ) *
        spectralNorm (matrixProduct (w.map (blockMatrix b i.castSucc))) := by
  rw [leadingBlock_word_submatrix b i M hupper w hw]
  exact spectralNorm_submatrix_le _ _

lemma finalBlock_word_norm_le {d r : ℕ} (b : Fin d → Fin (r + 1))
    (M : Set (Square d)) (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (w : List (Square d)) (hw : WordIn M w) :
    spectralNorm (matrixProduct (w.map (blockMatrix (lastSplit b) 1))) ≤
      (blockDim (lastSplit b) 1 : ℝ) *
        spectralNorm (matrixProduct (w.map (blockMatrix b (Fin.last r)))) := by
  rw [finalBlock_word_submatrix b M hupper w hw]
  exact spectralNorm_submatrix_le _ _

lemma leading_pair_word_norm_le {d r : ℕ} (b : Fin d → Fin (r + 1)) (i j : Fin r)
    (M : Set (Square d)) (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (w : List (Square d)) (hw : WordIn M w) :
    spectralNorm (matrixProduct (w.map (fun A => tensorMatrix (leadingBlockMap b i A)
      (leadingBlockMap b j A)))) ≤
      ((blockDim (leadingBlockLabel b) i * blockDim (leadingBlockLabel b) j : ℕ) : ℝ) *
        spectralNorm (matrixProduct (w.map (fun A => tensorMatrix (blockMatrix b i.castSucc A)
          (blockMatrix b j.castSucc A)))) := by
  rw [paired_matrixProduct, paired_matrixProduct,
    leadingBlock_word_submatrix b i M hupper w hw,
    leadingBlock_word_submatrix b j M hupper w hw]
  exact spectralNorm_tensor_submatrix_le _ _ _ _

lemma leading_final_pair_word_norm_le {d r : ℕ} (b : Fin d → Fin (r + 1)) (i : Fin r)
    (M : Set (Square d)) (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (w : List (Square d)) (hw : WordIn M w) :
    spectralNorm (matrixProduct (w.map (fun A => tensorMatrix (leadingBlockMap b i A)
      (blockMatrix (lastSplit b) 1 A)))) ≤
      ((blockDim (leadingBlockLabel b) i * blockDim (lastSplit b) 1 : ℕ) : ℝ) *
        spectralNorm (matrixProduct (w.map (fun A => tensorMatrix (blockMatrix b i.castSucc A)
          (blockMatrix b (Fin.last r) A)))) := by
  rw [paired_matrixProduct, paired_matrixProduct,
    leadingBlock_word_submatrix b i M hupper w hw,
    finalBlock_word_submatrix b M hupper w hw]
  exact spectralNorm_tensor_submatrix_le _ _ _ _

#print axioms leadingBlock_word_submatrix
#assert_trust kernel leadingBlock_word_submatrix
#print axioms leading_final_pair_word_norm_le
#assert_trust kernel leading_final_pair_word_norm_le

end NLA.MF06
