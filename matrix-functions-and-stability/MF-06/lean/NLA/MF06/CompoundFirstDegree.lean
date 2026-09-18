/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Every original coordinate occurs in an actual sorted singleton minor. Thus
the degree-one compound retains all original matrix entries and words. A
fixed dimension estimate suffices to recover the exact original radius.
-/
import NLA.MF06.CompoundRadius
import NLA.MF06.ImageWordComparison

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

lemma singleton_minor_covers {d : ℕ} (j : Fin d) :
    ∃ u : Fin (compoundDim d 1), minorCoordinate d 1 u 0 = j := by
  let e : Fin 1 ↪o Fin d :=
    { toFun := fun _ => j
      inj' := fun _ _ _ => Subsingleton.elim _ _
      map_rel_iff' := by
        intro a b
        constructor
        · intro _; exact le_of_eq (Subsingleton.elim a b)
        · intro _; exact le_rfl }
  let u : Fin (compoundDim d 1) :=
    Fintype.equivFin (ExteriorIndex d 1) (Set.powersetCard.ofFinEmbEquiv e)
  refine ⟨u, ?_⟩
  have he : minorCoordinate d 1 u = e := by
    unfold minorCoordinate compoundIndex
    -- Expose the two explicit inverse index maps: first the finite enumeration,
    -- then the equivalence from sorted embeddings to singleton subsets.
    change Set.powersetCard.ofFinEmbEquiv.symm
      ((Fintype.equivFin (ExteriorIndex d 1)).symm
        (Fintype.equivFin (ExteriorIndex d 1) (Set.powersetCard.ofFinEmbEquiv e))) = e
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact congrArg (fun f : Fin 1 ↪o Fin d => f 0) he

lemma spectralNorm_le_first_compound {d : ℕ} (A : Square d) :
    spectralNorm A ≤ (d : ℝ) * spectralNorm (compoundMatrix 1 A) := by
  apply spectralNorm_le_card_mul_entry_bound _ _ (spectralNorm_nonneg _)
  intro i j
  obtain ⟨u, hu⟩ := singleton_minor_covers i
  obtain ⟨v, hv⟩ := singleton_minor_covers j
  have he : compoundMatrix 1 A u v = A i j := by
    unfold compoundMatrix
    rw [Matrix.det_fin_one]
    -- A one-coordinate determinant is its sole entry; the remaining wrappers
    -- select the actual row and column of the original matrix.
    change A (minorCoordinate d 1 u 0) (minorCoordinate d 1 v 0) = A i j
    rw [hu, hv]
  rw [← he]
  exact spectralNorm_entry_bound _ u v

theorem compound_family_semantics {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) :
    (∀ k : ℕ, k ≤ d →
      IsCompact (compoundFamily k M) ∧ (compoundFamily k M).Nonempty ∧
      jointSpectralRadius (compoundFamily k M) ≤ jointSpectralRadius M ^ k) ∧
    jointSpectralRadius (compoundFamily 1 M) = jointSpectralRadius M := by
  refine ⟨fun k hk => ⟨hM.image (continuous_compoundMatrix k), hneM.image _,
    compound_radius_le_power hd M hM hneM k hk⟩, le_antisymm ?_ ?_⟩
  · simpa only [pow_one] using compound_radius_le_power hd M hM hneM 1 hd
  · have hdim := (compound_dimensions d 1).2 hd
    have hcomparison := image_radius_le_of_word_comparison hd hdim M hM hneM id
      (compoundMatrix 1) continuous_id (continuous_compoundMatrix 1)
      (max 1 (d : ℝ)) (le_max_left _ _) (by
        intro w _
        rw [List.map_id, compound_word_product]
        exact (spectralNorm_le_first_compound (matrixProduct w)).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (spectralNorm_nonneg _)))
    simpa only [Set.image_id, compoundFamily] using hcomparison

#print axioms compound_family_semantics
#assert_trust kernel compound_family_semantics

end NLA.MF06
