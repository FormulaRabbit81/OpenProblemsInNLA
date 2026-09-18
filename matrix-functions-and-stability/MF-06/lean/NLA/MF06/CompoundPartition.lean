/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Occupation allocations are ordered by their actual weight and then by their
fixed finite index. This labels the existing compound basis, without changing
its row or column order. Nonzero-minor rigidity proves the resulting compound
matrix is upper block triangular. The explicit occupation-fiber equivalence
then identifies each block's coordinate type with its allocation coordinates.
-/
import NLA.MF06.AllocationCoordinates
import NLA.MF06.OccupationWeights
import Mathlib.Data.Prod.Lex

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

def allocationOrderKey {d r k : ℕ} (b : Fin d → Fin r)
    (a : DegreeAllocation b k) : ℕ ×ₗ Fin (Fintype.card (DegreeAllocation b k)) :=
  toLex (allocationWeight b a.val, Fintype.equivFin (DegreeAllocation b k) a)

lemma allocationOrderKey_injective {d r k : ℕ} (b : Fin d → Fin r) :
    Function.Injective (allocationOrderKey (k := k) b) := by
  intro a c h
  apply (Fintype.equivFin (DegreeAllocation b k)).injective
  exact congrArg (fun z : ℕ ×ₗ Fin (Fintype.card (DegreeAllocation b k)) => (ofLex z).2) h

/-- This named order is used locally, leaving unrelated typeclass instances
and all frozen contracts unchanged. -/
abbrev allocationLinearOrder {d r : ℕ} (b : Fin d → Fin r) (k : ℕ) :
    LinearOrder (DegreeAllocation b k) :=
  LinearOrder.lift' (allocationOrderKey b) (allocationOrderKey_injective b)

def allocationOrderEquiv {d r : ℕ} (b : Fin d → Fin r) (k : ℕ) :
    Fin (Fintype.card (DegreeAllocation b k)) ≃ DegreeAllocation b k :=
  letI : LinearOrder (DegreeAllocation b k) := allocationLinearOrder b k
  (Fintype.orderIsoFinOfCardEq (DegreeAllocation b k) rfl).toEquiv

def allocationRank {d r k : ℕ} (b : Fin d → Fin r) :
    DegreeAllocation b k → Fin (Fintype.card (DegreeAllocation b k)) :=
  (allocationOrderEquiv b k).symm

lemma allocationRank_lt_of_weight_lt {d r k : ℕ} (b : Fin d → Fin r)
    (a c : DegreeAllocation b k) (h : allocationWeight b a.val < allocationWeight b c.val) :
    allocationRank b a < allocationRank b c := by
  -- The subtype also has inherited pointwise order instances. Select the
  -- named weight order at each superclass used by the order-isomorphism API.
  let : LinearOrder (DegreeAllocation b k) := allocationLinearOrder b k
  let : Preorder (DegreeAllocation b k) := (allocationLinearOrder b k).toPreorder
  let : LE (DegreeAllocation b k) := (allocationLinearOrder b k).toLE
  let : LT (DegreeAllocation b k) := (allocationLinearOrder b k).toLT
  have hac : a < c := by
    change allocationOrderKey b a < allocationOrderKey b c
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)
  exact (Fintype.orderIsoFinOfCardEq (DegreeAllocation b k) rfl).symm.strictMono hac

def compoundAllocationLabel {d r : ℕ} (b : Fin d → Fin r) (k : ℕ) :
    Fin (compoundDim d k) → Fin (Fintype.card (DegreeAllocation b k)) :=
  fun j => allocationRank b (degreeOccupation b (compoundIndex d k j))

lemma compoundAllocationLabel_surjective {d r : ℕ} (b : Fin d → Fin r) (k : ℕ) :
    Function.Surjective (compoundAllocationLabel b k) :=
  (allocationOrderEquiv b k).symm.surjective.comp
    (degreeOccupation_compoundIndex_surjective b)

lemma compoundAllocationLabel_eq_iff {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (j : Fin (compoundDim d k)) (t : Fin (Fintype.card (DegreeAllocation b k))) :
    compoundAllocationLabel b k j = t ↔
      degreeOccupation b (compoundIndex d k j) = allocationOrderEquiv b k t := by
  constructor
  · intro h
    calc
      degreeOccupation b (compoundIndex d k j) =
          allocationOrderEquiv b k ((allocationOrderEquiv b k).symm
            (degreeOccupation b (compoundIndex d k j))) :=
        ((allocationOrderEquiv b k).apply_symm_apply _).symm
      _ = allocationOrderEquiv b k t := congrArg (allocationOrderEquiv b k) h
  · intro h
    change (allocationOrderEquiv b k).symm (degreeOccupation b (compoundIndex d k j)) = t
    rw [h]
    exact (allocationOrderEquiv b k).symm_apply_apply t

lemma compoundMatrix_upperBlock {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (A : Square d) (hA : IsUpperBlockTriangular b A) :
    IsUpperBlockTriangular (compoundAllocationLabel b k) (compoundMatrix k A) := by
  intro i j hji
  by_contra hne
  obtain ⟨hle, hrigid⟩ := compound_nonzero_occupation b A hA i j hne
  have hij : compoundAllocationLabel b k i ≤ compoundAllocationLabel b k j := by
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact (allocationRank_lt_of_weight_lt b
        (degreeOccupation b (compoundIndex d k i))
        (degreeOccupation b (compoundIndex d k j)) hlt).le
    · exact le_of_eq (congrArg (allocationRank b) (hrigid heq))
  exact (not_le_of_gt hji) hij

/-- The block's actual frozen fiber coordinate, followed by the proved subset
decomposition, gives its tensor allocation coordinate. -/
def compoundBlockAllocationEquiv {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (t : Fin (Fintype.card (DegreeAllocation b k))) :
    Fin (blockDim (compoundAllocationLabel b k) t) ≃
      Fin (allocationDim b (allocationOrderEquiv b k t).val) :=
  (((Fintype.equivFin (BlockIndex (compoundAllocationLabel b k) t)).symm.trans
    (Equiv.subtypeEquivRight (fun j => compoundAllocationLabel_eq_iff b k j t))).trans
    (compoundAllocationFiberEquiv b (allocationOrderEquiv b k t))).trans
    (Fintype.equivFin (AllocationIndex b (allocationOrderEquiv b k t).val))

#print axioms compoundAllocationLabel_surjective
#assert_trust kernel compoundAllocationLabel_surjective
#print axioms compoundMatrix_upperBlock
#assert_trust kernel compoundMatrix_upperBlock
#print axioms compoundBlockAllocationEquiv
#assert_trust kernel compoundBlockAllocationEquiv

end NLA.MF06
