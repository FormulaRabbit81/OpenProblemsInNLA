/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The occupation fiber of a literal exterior subset is equivalent to the frozen
tensor allocation coordinate type. Both maps are constructed from actual local
subsets and the fixed exterior enumerations. Their inverse laws follow from
subset assembly/extraction, not from an assumed dimension equality. Degree-zero
factors remain singleton exterior index types.
-/
import NLA.MF06.OccupationSubsets
import NLA.MF06.AllocationDimensions

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06

/-- Assemble the actual local exterior subsets indexed by a tensor coordinate. -/
def allocationSubset {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (u : AllocationIndex b a) : ExteriorIndex d (allocationDegree b a) :=
  ⟨assembleBlockSubset b (fun i => (compoundIndex (blockDim b i) (a i).val (u i)).val), by
    change (assembleBlockSubset b
      (fun i => (compoundIndex (blockDim b i) (a i).val (u i)).val)).card = allocationDegree b a
    rw [card_assembleBlockSubset]
    exact Finset.sum_congr rfl (fun i _ =>
      (compoundIndex (blockDim b i) (a i).val (u i)).property)⟩

lemma localBlockSubset_allocationSubset {d r : ℕ} (b : Fin d → Fin r)
    (a : Allocation b) (u : AllocationIndex b a) (i : Fin r) :
    localBlockSubset b (allocationSubset b a u).val i =
      (compoundIndex (blockDim b i) (a i).val (u i)).val :=
  localBlockSubset_assemble b _ i

lemma occupationAllocation_allocationSubset {d r : ℕ} (b : Fin d → Fin r)
    (a : Allocation b) (u : AllocationIndex b a) :
    occupationAllocation b (allocationSubset b a u) = a := by
  funext i
  apply Fin.ext
  change (localBlockSubset b (allocationSubset b a u).val i).card = (a i).val
  rw [localBlockSubset_allocationSubset]
  exact (compoundIndex (blockDim b i) (a i).val (u i)).property

/-- Decode a subset of the stated occupation through the actual frozen local
exterior enumerations. The cardinality proof is obtained from the occupation
equality; it is not an extra assumption about the selected minors. -/
def allocationSubsetCoordinates {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (S : ExteriorIndex d (allocationDegree b a)) (hS : occupationAllocation b S = a) :
    AllocationIndex b a :=
  fun i => Fintype.equivFin (ExteriorIndex (blockDim b i) (a i).val)
    ⟨localBlockSubset b S.val i, congrArg (fun c : Allocation b => (c i).val) hS⟩

lemma compoundIndex_allocationSubsetCoordinates {d r : ℕ} (b : Fin d → Fin r)
    (a : Allocation b) (S : ExteriorIndex d (allocationDegree b a))
    (hS : occupationAllocation b S = a) (i : Fin r) :
    (compoundIndex (blockDim b i) (a i).val
      (allocationSubsetCoordinates b a S hS i)).val = localBlockSubset b S.val i :=
  congrArg Subtype.val ((Fintype.equivFin (ExteriorIndex (blockDim b i) (a i).val)).symm_apply_apply
    ⟨localBlockSubset b S.val i, congrArg (fun c : Allocation b => (c i).val) hS⟩)

lemma allocationSubset_coordinates {d r : ℕ} (b : Fin d → Fin r)
    (a : Allocation b) (S : ExteriorIndex d (allocationDegree b a))
    (hS : occupationAllocation b S = a) :
    allocationSubset b a (allocationSubsetCoordinates b a S hS) = S := by
  apply Subtype.ext
  apply localBlockSubset_injective b
  funext i
  rw [localBlockSubset_allocationSubset, compoundIndex_allocationSubsetCoordinates]

lemma allocationSubsetCoordinates_subset {d r : ℕ} (b : Fin d → Fin r)
    (a : Allocation b) (u : AllocationIndex b a) :
    allocationSubsetCoordinates b a (allocationSubset b a u)
      (occupationAllocation_allocationSubset b a u) = u := by
  funext i
  apply (Fintype.equivFin (ExteriorIndex (blockDim b i) (a i).val)).symm.injective
  apply Subtype.ext
  change (compoundIndex (blockDim b i) (a i).val
    (allocationSubsetCoordinates b a (allocationSubset b a u)
      (occupationAllocation_allocationSubset b a u) i)).val =
    (compoundIndex (blockDim b i) (a i).val (u i)).val
  rw [compoundIndex_allocationSubsetCoordinates, localBlockSubset_allocationSubset]

def allocationOccupationEquiv {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b) :
    {S : ExteriorIndex d (allocationDegree b a) // occupationAllocation b S = a} ≃
      AllocationIndex b a where
  toFun S := allocationSubsetCoordinates b a S.val S.property
  invFun u := ⟨allocationSubset b a u, occupationAllocation_allocationSubset b a u⟩
  left_inv S := Subtype.ext (allocationSubset_coordinates b a S.val S.property)
  right_inv u := allocationSubsetCoordinates_subset b a u

/-- The same proved equivalence with the externally fixed total degree. -/
def degreeAllocationOccupationEquiv {d r k : ℕ} (b : Fin d → Fin r)
    (a : DegreeAllocation b k) :
    {S : ExteriorIndex d k // degreeOccupation b S = a} ≃ AllocationIndex b a.val := by
  rcases a with ⟨a, ha⟩
  subst k
  exact (Equiv.subtypeEquivRight (fun S : ExteriorIndex d (allocationDegree b a) =>
    (show degreeOccupation b S = (⟨a, rfl⟩ : DegreeAllocation b (allocationDegree b a)) ↔
      occupationAllocation b S = a from Subtype.ext_iff))).trans
    (allocationOccupationEquiv b a)

lemma degreeOccupation_surjective {d r k : ℕ} (b : Fin d → Fin r) :
    Function.Surjective (degreeOccupation (k := k) b) := by
  intro a
  have hpos : 0 < Fintype.card (AllocationIndex b a.val) :=
    Nat.zero_lt_one.trans_le (allocation_dimensions b a.val).2.2
  obtain ⟨u⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨((degreeAllocationOccupationEquiv b a).symm u).val,
    ((degreeAllocationOccupationEquiv b a).symm u).property⟩

/-- Actual frozen compound coordinates, restricted to one occupation, decode
bijectively into the frozen tensor allocation coordinates. -/
def compoundAllocationFiberEquiv {d r k : ℕ} (b : Fin d → Fin r)
    (a : DegreeAllocation b k) :
    {j : Fin (compoundDim d k) // degreeOccupation b (compoundIndex d k j) = a} ≃
      AllocationIndex b a.val :=
  (Equiv.subtypeEquivOfSubtype (p := fun S : ExteriorIndex d k => degreeOccupation b S = a)
    (Fintype.equivFin (ExteriorIndex d k)).symm).trans
    (degreeAllocationOccupationEquiv b a)

lemma compoundAllocationFiber_card {d r k : ℕ} (b : Fin d → Fin r)
    (a : DegreeAllocation b k) :
    Fintype.card {j : Fin (compoundDim d k) // degreeOccupation b (compoundIndex d k j) = a} =
      allocationDim b a.val := Fintype.card_congr (compoundAllocationFiberEquiv b a)

lemma degreeOccupation_compoundIndex_surjective {d r k : ℕ} (b : Fin d → Fin r) :
    Function.Surjective (fun j : Fin (compoundDim d k) =>
      degreeOccupation b (compoundIndex d k j)) :=
  (degreeOccupation_surjective b).comp
    (Fintype.equivFin (ExteriorIndex d k)).symm.surjective

#print axioms allocationOccupationEquiv
#assert_trust kernel allocationOccupationEquiv
#print axioms compoundAllocationFiberEquiv
#assert_trust kernel compoundAllocationFiberEquiv
#print axioms degreeOccupation_compoundIndex_surjective
#assert_trust kernel degreeOccupation_compoundIndex_surjective

end NLA.MF06
