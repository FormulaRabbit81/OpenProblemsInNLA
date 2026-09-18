/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The selected coordinates are enumerated block by block using each frozen
sorted local minor. This enumeration is proved bijective onto the assembled
exterior subset. Comparing it with that subset's global sorted enumeration
gives the actual row/column equivalences required by determinant sign laws.
-/
import NLA.MF06.AllocationCoordinates

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06

def groupedSubsetCoordinate {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (u : AllocationIndex b a) (p : Σ i : Fin r, Fin (a i).val) : Fin d :=
  blockCoordinate b p.1 (minorCoordinate (blockDim b p.1) (a p.1).val (u p.1) p.2)

lemma groupedSubsetCoordinate_label {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (u : AllocationIndex b a) (p : Σ i : Fin r, Fin (a i).val) :
    b (groupedSubsetCoordinate b a u p) = p.1 := blockCoordinate_label b p.1 _

lemma groupedSubsetCoordinate_injective {d r : ℕ} (b : Fin d → Fin r)
    (a : Allocation b) (u : AllocationIndex b a) :
    Function.Injective (groupedSubsetCoordinate b a u) := by
  rintro ⟨i, v⟩ ⟨j, w⟩ h
  have hij : i = j := by
    calc
      i = b (groupedSubsetCoordinate b a u ⟨i, v⟩) :=
        (groupedSubsetCoordinate_label b a u ⟨i, v⟩).symm
      _ = b (groupedSubsetCoordinate b a u ⟨j, w⟩) := congrArg b h
      _ = j := groupedSubsetCoordinate_label b a u ⟨j, w⟩
  subst j
  have hvw : v = w := (minorCoordinate (blockDim b i) (a i).val (u i)).injective
    (blockCoordinate_injective b i h)
  exact congrArg (Sigma.mk i) hvw

lemma groupedSubsetCoordinate_mem {d r : ℕ} (b : Fin d → Fin r)
    (a : Allocation b) (u : AllocationIndex b a) (p : Σ i : Fin r, Fin (a i).val) :
    groupedSubsetCoordinate b a u p ∈ (allocationSubset b a u).val := by
  change blockCoordinate b p.1
    (minorCoordinate (blockDim b p.1) (a p.1).val (u p.1) p.2) ∈
      assembleBlockSubset b (fun i => (compoundIndex (blockDim b i) (a i).val (u i)).val)
  rw [blockCoordinate_mem_assemble]
  exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
    (compoundIndex (blockDim b p.1) (a p.1).val (u p.1)) _).mp ⟨p.2, rfl⟩

lemma groupedSubsetCoordinate_covers {d r : ℕ} (b : Fin d → Fin r)
    (a : Allocation b) (u : AllocationIndex b a) (j : Fin d)
    (hj : j ∈ (allocationSubset b a u).val) :
    ∃ p : Σ i : Fin r, Fin (a i).val, groupedSubsetCoordinate b a u p = j := by
  obtain ⟨⟨i, v⟩, he⟩ := (blockSigmaCoordinate b).surjective j
  have hlocal : v ∈ (compoundIndex (blockDim b i) (a i).val (u i)).val := by
    apply (blockCoordinate_mem_assemble b
      (fun t => (compoundIndex (blockDim b t) (a t).val (u t)).val) i v).mp
    change blockCoordinate b i v ∈ (allocationSubset b a u).val
    rw [← blockSigmaCoordinate_apply b i v, he]
    exact hj
  obtain ⟨q, hq⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
    (compoundIndex (blockDim b i) (a i).val (u i)) v).mpr hlocal
  change minorCoordinate (blockDim b i) (a i).val (u i) q = v at hq
  refine ⟨⟨i, q⟩, ?_⟩
  change blockCoordinate b i (minorCoordinate (blockDim b i) (a i).val (u i) q) = j
  rw [hq]
  exact he

def groupedSubsetEquiv {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (u : AllocationIndex b a) :
    (Σ i : Fin r, Fin (a i).val) ≃ (allocationSubset b a u).val :=
  Equiv.ofBijective (fun p => ⟨groupedSubsetCoordinate b a u p,
    groupedSubsetCoordinate_mem b a u p⟩)
    ⟨fun p q h => groupedSubsetCoordinate_injective b a u (congrArg Subtype.val h), by
      intro j
      obtain ⟨p, hp⟩ := groupedSubsetCoordinate_covers b a u j.val j.property
      exact ⟨p, Subtype.ext hp⟩⟩

/-- An actual equivalence from grouped selected coordinates to the globally
sorted minor coordinates. Distinct row/column subsets may give different signs. -/
def groupedMinorEquiv {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (u : AllocationIndex b a) :
    (Σ i : Fin r, Fin (a i).val) ≃ Fin (allocationDegree b a) :=
  (groupedSubsetEquiv b a u).trans
    (Set.powersetCard.orderIsoOfFin (allocationSubset b a u)).toEquiv.symm

lemma groupedMinorEquiv_apply {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (u : AllocationIndex b a) (p : Σ i : Fin r, Fin (a i).val) :
    Set.powersetCard.ofFinEmbEquiv.symm (allocationSubset b a u)
        (groupedMinorEquiv b a u p) = groupedSubsetCoordinate b a u p := by
  change ((Set.powersetCard.orderIsoOfFin (allocationSubset b a u)).toEquiv
    ((Set.powersetCard.orderIsoOfFin (allocationSubset b a u)).toEquiv.symm
      (groupedSubsetEquiv b a u p))).val = groupedSubsetCoordinate b a u p
  rw [Equiv.apply_symm_apply]
  rfl

/-- The single fiber of a sigma first projection has its original coordinate
type, including an empty type. -/
def sigmaFstFiberEquiv {α : Type*} (β : α → Type*) (i : α) :
    β i ≃ {p : Sigma β // p.1 = i} where
  toFun u := ⟨⟨i, u⟩, rfl⟩
  invFun p := p.property ▸ p.val.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨j, u⟩, h⟩
    dsimp only at h
    subst j
    rfl

#print axioms groupedSubsetEquiv
#assert_trust kernel groupedSubsetEquiv
#print axioms groupedMinorEquiv_apply
#assert_trust kernel groupedMinorEquiv_apply

end NLA.MF06
