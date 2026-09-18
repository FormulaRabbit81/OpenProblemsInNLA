/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Actual row and column subsets are separately regrouped by original block.
Mathlib's block-triangular determinant theorem gives the product of the actual
local minors. The proved reindexing norm identity accounts for both signs.
No invertibility, nonzero-minor hypothesis, or generic-position limit is used.
-/
import NLA.MF06.GroupedMinorCoordinates
import NLA.MF06.DeterminantNormReindex
import Mathlib.LinearAlgebra.Matrix.Block

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

def groupedMinorMatrix {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (u v : AllocationIndex b a) (A : Square d) :
    Matrix (Σ i : Fin r, Fin (a i).val) (Σ i : Fin r, Fin (a i).val) ℂ :=
  A.submatrix (groupedSubsetCoordinate b a u) (groupedSubsetCoordinate b a v)

lemma groupedMinorMatrix_upper {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (u v : AllocationIndex b a) (A : Square d) (hA : IsUpperBlockTriangular b A) :
    Matrix.BlockTriangular (groupedMinorMatrix b a u v A) Sigma.fst := by
  intro p q hpq
  exact hA (groupedSubsetCoordinate b a u p) (groupedSubsetCoordinate b a v q) (by
    rw [groupedSubsetCoordinate_label b a v q, groupedSubsetCoordinate_label b a u p]
    exact hpq)

lemma groupedMinorMatrix_block_det {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (u v : AllocationIndex b a) (A : Square d) (i : Fin r) :
    ((groupedMinorMatrix b a u v A).toSquareBlock Sigma.fst i).det =
      compoundMatrix (a i).val (blockMatrix b i A) (u i) (v i) := by
  classical
  let E := sigmaFstFiberEquiv (fun j : Fin r => Fin (a j).val) i
  calc
    ((groupedMinorMatrix b a u v A).toSquareBlock Sigma.fst i).det =
        (((groupedMinorMatrix b a u v A).toSquareBlock Sigma.fst i).submatrix E E).det :=
      (Matrix.det_submatrix_equiv_self E _).symm
    _ = compoundMatrix (a i).val (blockMatrix b i A) (u i) (v i) := rfl

/-- Empty diagonal fibers contribute their actual determinant, namely one. -/
lemma groupedMinorMatrix_det {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (u v : AllocationIndex b a) (A : Square d) (hA : IsUpperBlockTriangular b A) :
    (groupedMinorMatrix b a u v A).det =
      ∏ i : Fin r, compoundMatrix (a i).val (blockMatrix b i A) (u i) (v i) := by
  classical
  rw [(groupedMinorMatrix_upper b a u v A hA).det_fintype]
  exact Finset.prod_congr rfl (fun i _ => groupedMinorMatrix_block_det b a u v A i)

lemma norm_allocationSubset_minor {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (u v : AllocationIndex b a) (A : Square d) (hA : IsUpperBlockTriangular b A) :
    ‖(A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm (allocationSubset b a u))
      (Set.powersetCard.ofFinEmbEquiv.symm (allocationSubset b a v))).det‖ =
      ‖∏ i : Fin r, compoundMatrix (a i).val (blockMatrix b i A) (u i) (v i)‖ := by
  classical
  let M : Square (allocationDegree b a) :=
    A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm (allocationSubset b a u))
      (Set.powersetCard.ofFinEmbEquiv.symm (allocationSubset b a v))
  have hmatrix : M.submatrix (groupedMinorEquiv b a u) (groupedMinorEquiv b a v) =
      groupedMinorMatrix b a u v A := by
    ext p q
    change A (Set.powersetCard.ofFinEmbEquiv.symm (allocationSubset b a u)
        (groupedMinorEquiv b a u p))
      (Set.powersetCard.ofFinEmbEquiv.symm (allocationSubset b a v)
        (groupedMinorEquiv b a v q)) = _
    rw [groupedMinorEquiv_apply, groupedMinorEquiv_apply]
    rfl
  change ‖M.det‖ = _
  calc
    ‖M.det‖ = ‖(M.submatrix (groupedMinorEquiv b a u) (groupedMinorEquiv b a v)).det‖ :=
      (norm_det_submatrix_equiv_equiv (groupedMinorEquiv b a u) (groupedMinorEquiv b a v) M).symm
    _ = ‖(groupedMinorMatrix b a u v A).det‖ := congrArg (fun N => ‖N.det‖) hmatrix
    _ = ‖∏ i : Fin r, compoundMatrix (a i).val (blockMatrix b i A) (u i) (v i)‖ :=
      congrArg norm (groupedMinorMatrix_det b a u v A hA)

/-- The determinant norm identity for arbitrary original subsets in one
occupation fiber. Their local coordinates come from the proved decoding map. -/
lemma norm_minor_of_degreeOccupation {d r k : ℕ} (b : Fin d → Fin r)
    (A : Square d) (hA : IsUpperBlockTriangular b A) (a : DegreeAllocation b k)
    (S T : ExteriorIndex d k) (hS : degreeOccupation b S = a) (hT : degreeOccupation b T = a) :
    ‖(A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm S)
      (Set.powersetCard.ofFinEmbEquiv.symm T)).det‖ =
      ‖∏ i : Fin r, compoundMatrix (a.val i).val (blockMatrix b i A)
        (degreeAllocationOccupationEquiv b a ⟨S, hS⟩ i)
        (degreeAllocationOccupationEquiv b a ⟨T, hT⟩ i)‖ := by
  rcases a with ⟨a, ha⟩
  subst k
  have hS' : occupationAllocation b S = a := congrArg Subtype.val hS
  have hT' : occupationAllocation b T = a := congrArg Subtype.val hT
  change ‖(A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm S)
    (Set.powersetCard.ofFinEmbEquiv.symm T)).det‖ =
      ‖∏ i : Fin r, compoundMatrix (a i).val (blockMatrix b i A)
        (allocationSubsetCoordinates b a S hS' i) (allocationSubsetCoordinates b a T hT' i)‖
  have h := norm_allocationSubset_minor b a
    (allocationSubsetCoordinates b a S hS') (allocationSubsetCoordinates b a T hT') A hA
  rw [allocationSubset_coordinates b a S hS', allocationSubset_coordinates b a T hT'] at h
  exact h

lemma norm_compoundAllocationFiber_entry {d r k : ℕ} (b : Fin d → Fin r)
    (A : Square d) (hA : IsUpperBlockTriangular b A) (a : DegreeAllocation b k)
    (z w : {j : Fin (compoundDim d k) // degreeOccupation b (compoundIndex d k j) = a}) :
    ‖compoundMatrix k A z.val w.val‖ =
      ‖∏ i : Fin r, compoundMatrix (a.val i).val (blockMatrix b i A)
        (compoundAllocationFiberEquiv b a z i) (compoundAllocationFiberEquiv b a w i)‖ := by
  change ‖(A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm (compoundIndex d k z.val))
    (Set.powersetCard.ofFinEmbEquiv.symm (compoundIndex d k w.val))).det‖ =
      ‖∏ i : Fin r, compoundMatrix (a.val i).val (blockMatrix b i A)
        (degreeAllocationOccupationEquiv b a ⟨compoundIndex d k z.val, z.property⟩ i)
        (degreeAllocationOccupationEquiv b a ⟨compoundIndex d k w.val, w.property⟩ i)‖
  exact norm_minor_of_degreeOccupation b A hA a
    (compoundIndex d k z.val) (compoundIndex d k w.val) z.property w.property

#print axioms groupedMinorMatrix_det
#assert_trust kernel groupedMinorMatrix_det
#print axioms norm_minor_of_degreeOccupation
#assert_trust kernel norm_minor_of_degreeOccupation
#print axioms norm_compoundAllocationFiber_entry
#assert_trust kernel norm_compoundAllocationFiber_entry

end NLA.MF06
