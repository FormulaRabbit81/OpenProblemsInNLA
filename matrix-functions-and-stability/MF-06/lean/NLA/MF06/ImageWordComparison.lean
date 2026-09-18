/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

A pointwise comparison for words in the same original family transfers to
actual compact image-family growth, product boundedness, and spectral radius.
This separates structural coordinate identities from the root-limit argument.
-/
import NLA.MF06.GrowthComparison
import NLA.MF06.WordImages
import NLA.MF07.BlockComparison

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma image_familyGrowth_comparison {d m n : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (f : Square d → Square m)
    (g : Square d → Square n) (hf : Continuous f) (hg : Continuous g)
    (D : ℝ) (hD : 0 ≤ D)
    (hword : ∀ w, WordIn M w → spectralNorm (matrixProduct (w.map f)) ≤
      D * spectralNorm (matrixProduct (w.map g))) (k : ℕ) :
    familyGrowth (f '' M) k ≤ D * familyGrowth (g '' M) k := by
  obtain ⟨w, hwlen, hw, he⟩ := familyGrowth_attained (f '' M) (hM.image hf) (hneM.image f) k
  obtain ⟨v, hv, rfl⟩ := word_image_preimage M f w hw
  have hlen : v.length = k := by simpa only [List.length_map] using hwlen
  rw [← he]
  exact (hword v hv).trans (mul_le_mul_of_nonneg_left
    (word_le_familyGrowth (g '' M) (hM.image hg) k (v.map g)
      (by simpa only [List.length_map] using hlen) (word_image_in M g v hv)) hD)

lemma image_product_bounded_of_word_comparison {d m n : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (f : Square d → Square m)
    (g : Square d → Square n) (hf : Continuous f) (hg : Continuous g)
    (D : ℝ) (hD : 1 ≤ D)
    (hword : ∀ w, WordIn M w → spectralNorm (matrixProduct (w.map f)) ≤
      D * spectralNorm (matrixProduct (w.map g)))
    (hbounded : IsProductBounded (g '' M)) : IsProductBounded (f '' M) :=
  product_bounded_of_growth_comparison (g '' M) (f '' M) D hD
    (image_familyGrowth_comparison M hM hneM f g hf hg D (zero_le_one.trans hD) hword) hbounded

lemma image_radius_le_of_word_comparison {d m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (f : Square d → Square m) (g : Square d → Square n)
    (hf : Continuous f) (hg : Continuous g) (D : ℝ) (hD : 1 ≤ D)
    (hword : ∀ w, WordIn M w → spectralNorm (matrixProduct (w.map f)) ≤
      D * spectralNorm (matrixProduct (w.map g))) :
    jointSpectralRadius (f '' M) ≤ jointSpectralRadius (g '' M) :=
  radius_le_of_growth_comparison hn hm (g '' M) (f '' M) (hM.image hg) (hneM.image g)
    (hM.image hf) (hneM.image f) D hD
    (image_familyGrowth_comparison M hM hneM f g hf hg D (zero_le_one.trans hD) hword)

lemma spectralNorm_submatrix_le {m n : ℕ} (A : Square n) (e : Fin m → Fin n) :
    spectralNorm (A.submatrix e e) ≤ (m : ℝ) * spectralNorm A := by
  apply spectralNorm_le_card_mul_entry_bound _ _ (spectralNorm_nonneg A)
  intro i j
  exact spectralNorm_entry_bound A (e i) (e j)

lemma matrixProduct_submatrix_equiv {m n : ℕ} (e : Fin m ≃ Fin n)
    (w : List (Square n)) :
    matrixProduct (w.map (fun A => A.submatrix e e)) = (matrixProduct w).submatrix e e := by
  induction w with
  | nil =>
      simp only [List.map_nil, matrixProduct_nil]
      exact (Matrix.submatrix_one e e.injective).symm
  | cons A w ih =>
      simp only [List.map_cons, matrixProduct_cons, ih]
      exact Matrix.submatrix_mul_equiv _ _ e e e

/-- Reindexing is a literal matrix operation, and its fixed coordinate factor
cannot change product boundedness. This direction also covers empty spaces. -/
lemma product_bounded_reindexed {m n : ℕ} (e : Fin m ≃ Fin n)
    (M : Set (Square n)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hb : IsProductBounded M) :
    IsProductBounded ((fun A : Square n => A.submatrix e e) '' M) := by
  have hcont : Continuous (fun A : Square n => A.submatrix e e) :=
    continuous_id.matrix_submatrix e e
  have hb' : IsProductBounded ((id : Square n → Square n) '' M) := by simpa only [Set.image_id] using hb
  apply image_product_bounded_of_word_comparison M hM hneM _ id hcont continuous_id
    (max 1 (m : ℝ)) (le_max_left _ _) ?_ hb'
  intro w _
  rw [matrixProduct_submatrix_equiv, List.map_id]
  exact (spectralNorm_submatrix_le (matrixProduct w) e).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (spectralNorm_nonneg _))

#print axioms image_radius_le_of_word_comparison
#assert_trust kernel image_radius_le_of_word_comparison
#print axioms product_bounded_reindexed
#assert_trust kernel product_bounded_reindexed

end NLA.MF06
