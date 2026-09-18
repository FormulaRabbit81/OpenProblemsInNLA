/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Induction is on the number of original nonempty labeled blocks. The leading
family inherits both diagonal boundedness and every distinct paired radius.
C12 supplies strict decay for the grouped leading/final paired family; the
actual two-block word estimate then bounds the original complete family.
Neither a finite family assumption nor a bound on word length is introduced.
-/
import NLA.MF06.BinaryGrouping
import NLA.MF06.LeadingInheritance

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma spectralNorm_le_covering_block {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (hcover : ∀ j, b j = i) (A : Square d) :
    spectralNorm A ≤ (d : ℝ) * spectralNorm (blockMatrix b i A) := by
  apply spectralNorm_le_card_mul_entry_bound _ _ (spectralNorm_nonneg _)
  intro u v
  obtain ⟨u', hu⟩ := blockCoordinate_covers b i u (hcover u)
  obtain ⟨v', hv⟩ := blockCoordinate_covers b i v (hcover v)
  rw [← hu, ← hv]
  exact spectralNorm_entry_bound (blockMatrix b i A) u' v'

lemma covering_block_product_bounded {d r : ℕ} (hd : 1 ≤ d) (b : Fin d → Fin r)
    (i : Fin r) (hcover : ∀ j, b j = i)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (hb : IsProductBounded (diagonalFamily b i M)) : IsProductBounded M := by
  have hD : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hword (w : List (Square d)) (hw : WordIn M w) :
      spectralNorm (matrixProduct (w.map id)) ≤
        (d : ℝ) * spectralNorm (matrixProduct (w.map (blockMatrix b i))) := by
    rw [List.map_id, ← blockMatrix_matrixProduct b i M hupper w hw]
    exact spectralNorm_le_covering_block b i hcover _
  have hresult := image_product_bounded_of_word_comparison M hM hneM id (blockMatrix b i)
    continuous_id (continuous_blockMatrix b i) (d : ℝ) hD hword hb
  simpa only [Set.image_id] using hresult

/-- C13. Full finite-block nonresonance theorem, including every original
same-generator paired family and all positive ambient dimensions. -/
theorem block_nonresonance_product_bounded {d r : ℕ} (hd : 1 ≤ d)
    (b : Fin d → Fin r) (hb : Function.Surjective b) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (hdiag : ∀ i : Fin r, IsProductBounded (diagonalFamily b i M))
    (hpair : ∀ i j : Fin r, i ≠ j →
      jointSpectralRadius (pairedFamily M (blockMatrix b i) (blockMatrix b j)) < 1) :
    IsProductBounded M := by
  induction r generalizing d with
  | zero => exact Fin.elim0 (b ⟨0, hd⟩)
  | succ r ih =>
      by_cases hr : r = 0
      · subst r
        exact covering_block_product_bounded hd b 0 (fun j => by apply Fin.ext; omega)
          M hM hneM hupper (hdiag 0)
      · have hrpos : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
        have hsplit := lastSplit_surjective hrpos b hb
        have hleading : IsProductBounded (diagonalFamily (lastSplit b) 0 M) := by
          apply ih (blockDim_pos_of_surjective _ hsplit 0)
            (leadingBlockLabel b) (leadingBlockLabel_surjective b hb)
            (diagonalFamily (lastSplit b) 0 M)
            (diagonalFamily_isCompact _ _ M hM) (diagonalFamily_nonempty _ _ M hneM)
          · rintro A ⟨B, hB, rfl⟩
            exact leadingBlockLabel_upper b B (hupper B hB)
          · intro i
            exact leading_diagonal_product_bounded b i M hM hneM hupper (hdiag i.castSucc)
          · intro i j hij
            apply (leading_pair_radius_le b hb i j M hM hneM hupper).trans_lt
            apply hpair i.castSucc j.castSucc
            intro heq
            exact hij (Fin.castSucc_inj.mp heq)
        have hfinal := final_diagonal_product_bounded b M hM hneM hupper (hdiag (Fin.last r))
        have hgrouped := grouped_leading_final_radius_lt hrpos b hb M hM hneM hupper
          (fun i => hpair i.castSucc (Fin.last r) (Fin.castSucc_ne_last i))
        exact binary_partition_product_bounded (lastSplit b) hsplit M hM hneM
          (fun A hA => lastSplit_upper b A (hupper A hA)) hleading hfinal hgrouped

#print axioms block_nonresonance_product_bounded
#assert_trust kernel block_nonresonance_product_bounded

end NLA.MF06
