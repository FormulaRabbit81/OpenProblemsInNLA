/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The full paired family's radius is controlled by its actual tensor diagonal
blocks. Exact word compression and a fixed coordinate norm factor give the
radius comparison. The previously proved C12 formula then turns strict decay
of every original paired diagonal family into strict decay of the grouped pair.
-/
import NLA.MF06.TensorBlockGeometry
import NLA.MF06.PairedWords
import NLA.MF06.BlockRadius

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma tensor_diagonal_word_submatrix {d m n r : ℕ} (b : Fin m → Fin r) (i : Fin r)
    (M : Set (Square d)) (f : Square d → Square m) (g : Square d → Square n)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b (f A))
    (w : List (Square d)) (hw : WordIn M w) :
    matrixProduct (w.map (fun A => blockMatrix (tensorBlockLabel b n) i (tensorMatrix (f A) (g A)))) =
      (matrixProduct (w.map (fun A => tensorMatrix (blockMatrix b i (f A)) (g A)))).submatrix
        (tensorBlockCoordinate b n i) (tensorBlockCoordinate b n i) := by
  have hfirst : ∀ A ∈ f '' M, IsUpperBlockTriangular b A := by
    rintro A ⟨B, hB, rfl⟩
    exact hupper B hB
  have hpaired : ∀ A ∈ pairedFamily M f g, IsUpperBlockTriangular (tensorBlockLabel b n) A := by
    rintro A ⟨B, hB, rfl⟩
    exact tensorBlock_upper b (f B) (g B) (hupper B hB)
  have hfword := blockMatrix_matrixProduct b i (f '' M) hfirst (w.map f)
    (word_image_in M f w hw)
  simp only [List.map_map, Function.comp_def] at hfword
  have hpairword := blockMatrix_matrixProduct (tensorBlockLabel b n) i (pairedFamily M f g)
    hpaired (w.map (fun A => tensorMatrix (f A) (g A)))
      (word_image_in M (fun A => tensorMatrix (f A) (g A)) w hw)
  calc
    matrixProduct (w.map (fun A => blockMatrix (tensorBlockLabel b n) i (tensorMatrix (f A) (g A)))) =
        blockMatrix (tensorBlockLabel b n) i
          (matrixProduct (w.map (fun A => tensorMatrix (f A) (g A)))) := by
      simpa only [List.map_map, Function.comp_def] using hpairword.symm
    _ = blockMatrix (tensorBlockLabel b n) i
        (tensorMatrix (matrixProduct (w.map f)) (matrixProduct (w.map g))) := by
      rw [paired_matrixProduct]
    _ = (tensorMatrix (blockMatrix b i (matrixProduct (w.map f)))
        (matrixProduct (w.map g))).submatrix (tensorBlockCoordinate b n i) (tensorBlockCoordinate b n i) :=
      tensorBlock_submatrix b i _ _
    _ = _ := by rw [hfword, paired_matrixProduct]

lemma tensor_diagonal_radius_le {d m n r : ℕ} (hn : 1 ≤ n)
    (b : Fin m → Fin r) (hb : Function.Surjective b) (i : Fin r)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (f : Square d → Square m) (g : Square d → Square n)
    (hf : Continuous f) (hg : Continuous g)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b (f A)) :
    jointSpectralRadius (diagonalFamily (tensorBlockLabel b n) i (pairedFamily M f g)) ≤
      jointSpectralRadius (pairedFamily M (fun A => blockMatrix b i (f A)) g) := by
  let H : Square d → Square (blockDim (tensorBlockLabel b n) i) := fun A =>
    blockMatrix (tensorBlockLabel b n) i (tensorMatrix (f A) (g A))
  let G : Square d → Square (blockDim b i * n) := fun A => tensorMatrix (blockMatrix b i (f A)) (g A)
  have hH : Continuous H := (continuous_blockMatrix (tensorBlockLabel b n) i).comp
    (continuous_tensorMatrix.comp (hf.prodMk hg))
  have hG : Continuous G := continuous_tensorMatrix.comp
    (((continuous_blockMatrix b i).comp hf).prodMk hg)
  have hdimH := blockDim_pos_of_surjective (tensorBlockLabel b n) (tensorBlockLabel_surjective b hb hn) i
  have hdimG : 1 ≤ blockDim b i * n :=
    one_le_mul_of_one_le_of_one_le (blockDim_pos_of_surjective b hb i) hn
  have hD : (1 : ℝ) ≤ (blockDim (tensorBlockLabel b n) i : ℝ) := by exact_mod_cast hdimH
  have hword (w : List (Square d)) (hw : WordIn M w) :
      spectralNorm (matrixProduct (w.map H)) ≤ (blockDim (tensorBlockLabel b n) i : ℝ) *
        spectralNorm (matrixProduct (w.map G)) := by
    change spectralNorm (matrixProduct (w.map (fun A =>
      blockMatrix (tensorBlockLabel b n) i (tensorMatrix (f A) (g A))))) ≤ _
    rw [tensor_diagonal_word_submatrix b i M f g hupper w hw]
    exact spectralNorm_submatrix_le _ _
  have hresult := image_radius_le_of_word_comparison hdimH hdimG M hM hneM H G hH hG
    (blockDim (tensorBlockLabel b n) i : ℝ) hD hword
  simpa only [diagonalFamily, pairedFamily, Set.image_image, Function.comp_def, H, G] using hresult

/-- Strict paired decay survives grouping all the first-factor blocks. -/
lemma paired_radius_lt_one_of_blocks {d m n r : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (b : Fin m → Fin r) (hb : Function.Surjective b)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (f : Square d → Square m) (g : Square d → Square n)
    (hf : Continuous f) (hg : Continuous g)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b (f A))
    (hdiag : ∀ i, jointSpectralRadius (pairedFamily M (fun A => blockMatrix b i (f A)) g) < 1) :
    jointSpectralRadius (pairedFamily M f g) < 1 := by
  have hpaired : ∀ A ∈ pairedFamily M f g, IsUpperBlockTriangular (tensorBlockLabel b n) A := by
    rintro A ⟨B, hB, rfl⟩
    exact tensorBlock_upper b (f B) (g B) (hupper B hB)
  rw [block_radius_formula (one_le_mul_of_one_le_of_one_le hm hn) (tensorBlockLabel b n)
    (tensorBlockLabel_surjective b hb hn) (pairedFamily M f g)
    (pairedFamily_isCompact M hM f g hf hg) (pairedFamily_nonempty M hneM f g) hpaired]
  have hne : (Set.range (fun i : Fin r =>
      jointSpectralRadius (diagonalFamily (tensorBlockLabel b n) i (pairedFamily M f g)))).Nonempty :=
    ⟨_, ⟨b ⟨0, hm⟩, rfl⟩⟩
  apply ((Set.finite_range _).csSup_lt_iff hne).mpr
  rintro z ⟨i, rfl⟩
  exact (tensor_diagonal_radius_le hn b hb i M hM hneM f g hf hg hupper).trans_lt (hdiag i)

#print axioms paired_radius_lt_one_of_blocks
#assert_trust kernel paired_radius_lt_one_of_blocks

end NLA.MF06
