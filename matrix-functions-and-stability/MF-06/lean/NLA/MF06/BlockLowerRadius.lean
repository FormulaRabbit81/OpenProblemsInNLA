/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The operator-entry norm bounds and growth framework retain the mathematical
attribution to Matthew J. Colbrook recorded in the unchanged MF05/MF07 sources.

Actual diagonal words lift to original words. Their norm comparison has a
fixed dimension factor, so the already proved radius comparison removes it.
This proves the lower direction of C12, not the complete triangular formula.
-/
import NLA.MF06.BlockAlgebra
import NLA.MF06.WordImages
import NLA.MF06.GrowthComparison
import NLA.MF07.BlockComparison

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

lemma spectralNorm_blockMatrix_le {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (A : Square d) :
    spectralNorm (blockMatrix b i A) ≤ (blockDim b i : ℝ) * spectralNorm A := by
  apply spectralNorm_le_card_mul_entry_bound (blockMatrix b i A) (spectralNorm A)
    (spectralNorm_nonneg A)
  intro u v
  exact spectralNorm_entry_bound A (blockCoordinate b i u) (blockCoordinate b i v)

lemma familyGrowth_diagonal_le {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) (n : ℕ) :
    familyGrowth (diagonalFamily b i M) n ≤ (blockDim b i : ℝ) * familyGrowth M n := by
  obtain ⟨w, hw, hword, he⟩ := familyGrowth_attained (diagonalFamily b i M)
    (diagonalFamily_isCompact b i M hM) (diagonalFamily_nonempty b i M hneM) n
  obtain ⟨v, hv, rfl⟩ := word_image_preimage M (blockMatrix b i) w hword
  have hvn : v.length = n := by simpa only [List.length_map] using hw
  rw [← he, ← blockMatrix_matrixProduct b i M hupper v hv]
  exact (spectralNorm_blockMatrix_le b i (matrixProduct v)).trans
    (mul_le_mul_of_nonneg_left (word_le_familyGrowth M hM n v hvn hv) (Nat.cast_nonneg _))

lemma diagonal_radius_le {d r : ℕ} (hd : 1 ≤ d) (b : Fin d → Fin r)
    (hb : Function.Surjective b) (i : Fin r) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) :
    jointSpectralRadius (diagonalFamily b i M) ≤ jointSpectralRadius M := by
  have hi := blockDim_pos_of_surjective b hb i
  have hiR : 1 ≤ (blockDim b i : ℝ) := by exact_mod_cast hi
  exact radius_le_of_growth_comparison hd hi M (diagonalFamily b i M) hM hneM
    (diagonalFamily_isCompact b i M hM) (diagonalFamily_nonempty b i M hneM)
    (blockDim b i : ℝ) hiR (familyGrowth_diagonal_le b i M hM hneM hupper)

lemma diagonal_sup_radius_le {d r : ℕ} (hd : 1 ≤ d) (b : Fin d → Fin r)
    (hb : Function.Surjective b) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) :
    sSup (Set.range (fun i : Fin r => jointSpectralRadius (diagonalFamily b i M))) ≤
      jointSpectralRadius M := by
  have hne : (Set.range (fun i : Fin r =>
      jointSpectralRadius (diagonalFamily b i M))).Nonempty :=
    ⟨jointSpectralRadius (diagonalFamily b (b ⟨0, hd⟩) M), ⟨b ⟨0, hd⟩, rfl⟩⟩
  refine csSup_le hne ?_
  rintro z ⟨i, rfl⟩
  exact diagonal_radius_le hd b hb i M hM hneM hupper

#print axioms diagonal_sup_radius_le
#assert_trust kernel diagonal_sup_radius_le

end NLA.MF06
