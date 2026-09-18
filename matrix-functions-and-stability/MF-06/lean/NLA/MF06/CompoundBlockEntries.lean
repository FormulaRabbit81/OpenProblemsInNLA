/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The grouped determinant identity is now expressed in the actual frozen block
and allocation matrix coordinates. Separate determinant signs disappear only
inside proved entry norms. Actual Euclidean operator-entry estimates give
fixed, word-independent comparison constants in both directions.
-/
import NLA.MF06.CompoundPartition
import NLA.MF06.GroupedMinorDeterminant
import NLA.MF06.ImageWordComparison

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma allocationCoordinate_compoundBlockAllocationEquiv {d r : ℕ}
    (b : Fin d → Fin r) (k : ℕ) (t : Fin (Fintype.card (DegreeAllocation b k)))
    (p : Fin (blockDim (compoundAllocationLabel b k) t)) :
    allocationCoordinate b (allocationOrderEquiv b k t).val (compoundBlockAllocationEquiv b k t p) =
      compoundAllocationFiberEquiv b (allocationOrderEquiv b k t)
        ⟨blockCoordinate (compoundAllocationLabel b k) t p,
          (compoundAllocationLabel_eq_iff b k _ t).mp
            (blockCoordinate_label (compoundAllocationLabel b k) t p)⟩ := by
  change (Fintype.equivFin (AllocationIndex b (allocationOrderEquiv b k t).val)).symm
    ((Fintype.equivFin (AllocationIndex b (allocationOrderEquiv b k t).val)) _) = _
  exact (Fintype.equivFin (AllocationIndex b (allocationOrderEquiv b k t).val)).symm_apply_apply _

lemma norm_compoundBlock_entry {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (A : Square d) (hA : IsUpperBlockTriangular b A)
    (t : Fin (Fintype.card (DegreeAllocation b k)))
    (p q : Fin (blockDim (compoundAllocationLabel b k) t)) :
    ‖blockMatrix (compoundAllocationLabel b k) t (compoundMatrix k A) p q‖ =
      ‖allocationMatrix b (allocationOrderEquiv b k t).val A
        (compoundBlockAllocationEquiv b k t p) (compoundBlockAllocationEquiv b k t q)‖ := by
  change ‖compoundMatrix k A
    (blockCoordinate (compoundAllocationLabel b k) t p)
    (blockCoordinate (compoundAllocationLabel b k) t q)‖ =
      ‖∏ i : Fin r,
        compoundMatrix ((allocationOrderEquiv b k t).val i).val (blockMatrix b i A)
          (allocationCoordinate b (allocationOrderEquiv b k t).val
            (compoundBlockAllocationEquiv b k t p) i)
          (allocationCoordinate b (allocationOrderEquiv b k t).val
            (compoundBlockAllocationEquiv b k t q) i)‖
  rw [allocationCoordinate_compoundBlockAllocationEquiv b k t p,
    allocationCoordinate_compoundBlockAllocationEquiv b k t q]
  -- Supply both fiber coordinates explicitly. Inferring them through their
  -- projections would unfold the entire finite occupation enumeration.
  exact norm_compoundAllocationFiber_entry b A hA (allocationOrderEquiv b k t)
    ⟨blockCoordinate (compoundAllocationLabel b k) t p,
      (compoundAllocationLabel_eq_iff b k _ t).mp
        (blockCoordinate_label (compoundAllocationLabel b k) t p)⟩
    ⟨blockCoordinate (compoundAllocationLabel b k) t q,
      (compoundAllocationLabel_eq_iff b k _ t).mp
        (blockCoordinate_label (compoundAllocationLabel b k) t q)⟩

lemma spectralNorm_le_of_entry_norm {m n : ℕ} (A : Square m) (B : Square n)
    (e : Fin m → Fin n) (h : ∀ i j, ‖A i j‖ = ‖B (e i) (e j)‖) :
    spectralNorm A ≤ (m : ℝ) * spectralNorm B := by
  apply spectralNorm_le_card_mul_entry_bound A _ (spectralNorm_nonneg B)
  intro i j
  rw [h i j]
  exact spectralNorm_entry_bound B (e i) (e j)

lemma spectralNorm_comparison_of_entry_norm_equiv {m n : ℕ}
    (A : Square m) (B : Square n) (e : Fin m ≃ Fin n)
    (h : ∀ i j, ‖A i j‖ = ‖B (e i) (e j)‖) :
    spectralNorm A ≤ (m : ℝ) * spectralNorm B ∧
      spectralNorm B ≤ (n : ℝ) * spectralNorm A := by
  refine ⟨spectralNorm_le_of_entry_norm A B e h, ?_⟩
  apply spectralNorm_le_of_entry_norm B A e.symm
  intro i j
  simpa only [Equiv.apply_symm_apply] using (h (e.symm i) (e.symm j)).symm

lemma compoundBlock_norm_comparison {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (A : Square d) (hA : IsUpperBlockTriangular b A)
    (t : Fin (Fintype.card (DegreeAllocation b k))) :
    spectralNorm (blockMatrix (compoundAllocationLabel b k) t (compoundMatrix k A)) ≤
        (blockDim (compoundAllocationLabel b k) t : ℝ) *
          spectralNorm (allocationMatrix b (allocationOrderEquiv b k t).val A) ∧
      spectralNorm (allocationMatrix b (allocationOrderEquiv b k t).val A) ≤
        (allocationDim b (allocationOrderEquiv b k t).val : ℝ) *
          spectralNorm (blockMatrix (compoundAllocationLabel b k) t (compoundMatrix k A)) :=
  spectralNorm_comparison_of_entry_norm_equiv _ _ (compoundBlockAllocationEquiv b k t)
    (norm_compoundBlock_entry b k A hA t)

#print axioms norm_compoundBlock_entry
#assert_trust kernel norm_compoundBlock_entry
#print axioms compoundBlock_norm_comparison
#assert_trust kernel compoundBlock_norm_comparison

end NLA.MF06
