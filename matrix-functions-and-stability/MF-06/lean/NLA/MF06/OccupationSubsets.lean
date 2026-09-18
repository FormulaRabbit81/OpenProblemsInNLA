/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

An exterior subset is decomposed along the actual original coordinate fibers.
The two maps below are inverse on all finite subsets, before any cardinality
constraint is imposed. Consequently the occupation allocation and its degree
are proved facts about those subsets. Empty fibers and degree zero are retained.
-/
import NLA.MF06.BlockCoordinates
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06

/-- The disjoint collection of frozen original block coordinates is exactly
the original coordinate space. No contiguous ordering of its fibers is used. -/
def blockSigmaCoordinate {d r : ℕ} (b : Fin d → Fin r) :
    (Σ i : Fin r, Fin (blockDim b i)) ≃ Fin d :=
  (Equiv.sigmaCongrRight fun i => (Fintype.equivFin (BlockIndex b i)).symm).trans
    (Equiv.sigmaFiberEquiv b)

lemma blockSigmaCoordinate_apply {d r : ℕ} (b : Fin d → Fin r)
    (i : Fin r) (u : Fin (blockDim b i)) :
    blockSigmaCoordinate b ⟨i, u⟩ = blockCoordinate b i u := rfl

def localBlockSubset {d r : ℕ} (b : Fin d → Fin r) (S : Finset (Fin d))
    (i : Fin r) : Finset (Fin (blockDim b i)) :=
  Finset.univ.filter (fun u => blockCoordinate b i u ∈ S)

def assembleBlockSubset {d r : ℕ} (b : Fin d → Fin r)
    (F : ∀ i : Fin r, Finset (Fin (blockDim b i))) : Finset (Fin d) :=
  (Finset.univ.sigma F).map (blockSigmaCoordinate b).toEmbedding

lemma blockCoordinate_mem_assemble {d r : ℕ} (b : Fin d → Fin r)
    (F : ∀ i : Fin r, Finset (Fin (blockDim b i)))
    (i : Fin r) (u : Fin (blockDim b i)) :
    blockCoordinate b i u ∈ assembleBlockSubset b F ↔ u ∈ F i := by
  classical
  change blockSigmaCoordinate b ⟨i, u⟩ ∈
    (Finset.univ.sigma F).map (blockSigmaCoordinate b).toEmbedding ↔ u ∈ F i
  constructor
  · intro h
    obtain ⟨v, hv, he⟩ := Finset.mem_map.mp h
    have hvu : v = ⟨i, u⟩ := (blockSigmaCoordinate b).injective he
    subst v
    exact (Finset.mem_sigma.mp hv).2
  · intro hu
    exact Finset.mem_map.mpr ⟨⟨i, u⟩,
      Finset.mem_sigma.mpr ⟨Finset.mem_univ i, hu⟩, rfl⟩

lemma localBlockSubset_assemble {d r : ℕ} (b : Fin d → Fin r)
    (F : ∀ i : Fin r, Finset (Fin (blockDim b i))) (i : Fin r) :
    localBlockSubset b (assembleBlockSubset b F) i = F i := by
  ext u
  simp only [localBlockSubset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact blockCoordinate_mem_assemble b F i u

lemma assembleBlockSubset_local {d r : ℕ} (b : Fin d → Fin r)
    (S : Finset (Fin d)) :
    assembleBlockSubset b (localBlockSubset b S) = S := by
  ext j
  obtain ⟨⟨i, u⟩, hj⟩ := (blockSigmaCoordinate b).surjective j
  rw [← hj]
  change blockCoordinate b i u ∈ assembleBlockSubset b (localBlockSubset b S) ↔
    blockCoordinate b i u ∈ S
  rw [blockCoordinate_mem_assemble]
  simp only [localBlockSubset, Finset.mem_filter, Finset.mem_univ, true_and]

lemma localBlockSubset_injective {d r : ℕ} (b : Fin d → Fin r) :
    Function.Injective (localBlockSubset b) := by
  intro S T h
  calc
    S = assembleBlockSubset b (localBlockSubset b S) :=
      (assembleBlockSubset_local b S).symm
    _ = assembleBlockSubset b (localBlockSubset b T) := congrArg (assembleBlockSubset b) h
    _ = T := assembleBlockSubset_local b T

lemma card_assembleBlockSubset {d r : ℕ} (b : Fin d → Fin r)
    (F : ∀ i : Fin r, Finset (Fin (blockDim b i))) :
    (assembleBlockSubset b F).card = ∑ i : Fin r, (F i).card := by
  simp only [assembleBlockSubset, Finset.card_map, Finset.card_sigma]

lemma sum_card_localBlockSubset {d r : ℕ} (b : Fin d → Fin r)
    (S : Finset (Fin d)) :
    (∑ i : Fin r, (localBlockSubset b S i).card) = S.card := by
  rw [← card_assembleBlockSubset, assembleBlockSubset_local]

/-- The occupation is defined from the actual selected local coordinates.
The `Fin` bound follows from their inclusion in the complete block fiber. -/
def occupationAllocation {d r k : ℕ} (b : Fin d → Fin r)
    (S : ExteriorIndex d k) : Allocation b :=
  fun i => ⟨(localBlockSubset b S.val i).card, Nat.lt_succ_of_le (by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (localBlockSubset b S.val i))⟩

lemma occupationAllocation_val {d r k : ℕ} (b : Fin d → Fin r)
    (S : ExteriorIndex d k) (i : Fin r) :
    (occupationAllocation b S i).val = (localBlockSubset b S.val i).card := rfl

lemma occupationAllocation_degree {d r k : ℕ} (b : Fin d → Fin r)
    (S : ExteriorIndex d k) : allocationDegree b (occupationAllocation b S) = k :=
  (sum_card_localBlockSubset b S.val).trans S.property

def degreeOccupation {d r k : ℕ} (b : Fin d → Fin r)
    (S : ExteriorIndex d k) : DegreeAllocation b k :=
  ⟨occupationAllocation b S, occupationAllocation_degree b S⟩

#print axioms blockCoordinate_mem_assemble
#assert_trust kernel blockCoordinate_mem_assemble
#print axioms assembleBlockSubset_local
#assert_trust kernel assembleBlockSubset_local
#print axioms occupationAllocation_degree
#assert_trust kernel occupationAllocation_degree

end NLA.MF06
