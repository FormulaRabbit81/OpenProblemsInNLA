/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The sorted minor coordinates and the local-subset occupation describe the same
selected original coordinates. Explicit restricted equivalences prove their
fiber counts equal. Finite-sum regrouping identifies the two weight formulas,
so the nonzero-minor matching constraints apply to the actual occupation.
-/
import NLA.MF06.MinorTransition
import NLA.MF06.OccupationSubsets

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

private def selectedBlockSwap {d r : ℕ} (b : Fin d → Fin r)
    (S : Finset (Fin d)) (i : Fin r) :
    {j : BlockIndex b i // j.val ∈ S} ≃ {j : S // b j.val = i} where
  toFun j := ⟨⟨j.val.val, j.property⟩, j.val.property⟩
  invFun j := ⟨⟨j.val.val, j.property⟩, j.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The local subset coordinate and selected original-coordinate fiber are
related by the frozen block enumeration itself. -/
def selectedBlockSubsetEquiv {d r : ℕ} (b : Fin d → Fin r)
    (S : Finset (Fin d)) (i : Fin r) :
    (localBlockSubset b S i) ≃ {j : S // b j.val = i} :=
  ((Equiv.subtypeEquivRight (fun u : Fin (blockDim b i) =>
      (show u ∈ localBlockSubset b S i ↔ blockCoordinate b i u ∈ S by
        simp only [localBlockSubset, Finset.mem_filter, Finset.mem_univ, true_and]))).trans
    (Equiv.subtypeEquivOfSubtype (p := fun j : BlockIndex b i => j.val ∈ S)
      (Fintype.equivFin (BlockIndex b i)).symm)).trans (selectedBlockSwap b S i)

lemma selectedBlockSubsetEquiv_apply {d r : ℕ} (b : Fin d → Fin r)
    (S : Finset (Fin d)) (i : Fin r) (u : localBlockSubset b S i) :
    (selectedBlockSubsetEquiv b S i u).val.val = blockCoordinate b i u.val := rfl

lemma sortedSubset_labelCount {d r k : ℕ} (b : Fin d → Fin r)
    (S : ExteriorIndex d k) (i : Fin r) :
    minorLabelCount b (Set.powersetCard.ofFinEmbEquiv.symm S) i =
      (occupationAllocation b S i).val := by
  let E : {j : Fin k // b (Set.powersetCard.ofFinEmbEquiv.symm S j) = i} ≃
      {j : S.val // b j.val = i} :=
    Equiv.subtypeEquivOfSubtype (p := fun j : S.val => b j.val = i)
      (Set.powersetCard.orderIsoOfFin S).toEquiv
  calc
    minorLabelCount b (Set.powersetCard.ofFinEmbEquiv.symm S) i =
        Fintype.card {j : S.val // b j.val = i} := Fintype.card_congr E
    _ = Fintype.card (localBlockSubset b S.val i) :=
      (Fintype.card_congr (selectedBlockSubsetEquiv b S.val i)).symm
    _ = (occupationAllocation b S i).val := Fintype.card_coe _

lemma minorCoordinate_labelCount {d r k : ℕ} (b : Fin d → Fin r)
    (j : Fin (compoundDim d k)) (i : Fin r) :
    minorLabelCount b (minorCoordinate d k j) i =
      (occupationAllocation b (compoundIndex d k j) i).val :=
  sortedSubset_labelCount b (compoundIndex d k j) i

def allocationWeight {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b) : ℕ :=
  ∑ i : Fin r, i.val * (a i).val

lemma minorLabelWeight_eq_sum_counts {d r : ℕ} {ι : Type*} [Fintype ι]
    (b : Fin d → Fin r) (e : ι → Fin d) :
    minorLabelWeight b e = ∑ i : Fin r, i.val * minorLabelCount b e i := by
  calc
    minorLabelWeight b e = ∑ i : Fin r, ∑ _j : {j : ι // b (e j) = i}, i.val :=
      (Fintype.sum_fiberwise' (fun j : ι => b (e j)) (fun i : Fin r => i.val)).symm
    _ = ∑ i : Fin r, i.val * minorLabelCount b e i := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, minorLabelCount,
        Nat.mul_comm, Nat.cast_id]

lemma minorCoordinate_labelWeight {d r k : ℕ} (b : Fin d → Fin r)
    (j : Fin (compoundDim d k)) :
    minorLabelWeight b (minorCoordinate d k j) =
      allocationWeight b (occupationAllocation b (compoundIndex d k j)) := by
  rw [minorLabelWeight_eq_sum_counts]
  exact Finset.sum_congr rfl (fun i _ =>
    congrArg (fun c : ℕ => i.val * c) (minorCoordinate_labelCount b j i))

/-- A nonzero compound entry has increasing occupation weight. If the weights
tie, the actual allocations coincide, not merely their total degree. -/
lemma compound_nonzero_occupation {d r k : ℕ} (b : Fin d → Fin r)
    (A : Square d) (hA : IsUpperBlockTriangular b A)
    (i j : Fin (compoundDim d k)) (hne : compoundMatrix k A i j ≠ 0) :
    allocationWeight b (occupationAllocation b (compoundIndex d k i)) ≤
      allocationWeight b (occupationAllocation b (compoundIndex d k j)) ∧
    (allocationWeight b (occupationAllocation b (compoundIndex d k i)) =
        allocationWeight b (occupationAllocation b (compoundIndex d k j)) →
      degreeOccupation b (compoundIndex d k i) = degreeOccupation b (compoundIndex d k j)) := by
  have hweight := minor_weight_le_of_nonzero b A hA
    (minorCoordinate d k i) (minorCoordinate d k j) hne
  rw [minorCoordinate_labelWeight, minorCoordinate_labelWeight] at hweight
  refine ⟨hweight, ?_⟩
  intro heq
  have heq' : minorLabelWeight b (minorCoordinate d k i) =
      minorLabelWeight b (minorCoordinate d k j) := by
    rw [minorCoordinate_labelWeight, minorCoordinate_labelWeight]
    exact heq
  apply Subtype.ext
  funext t
  apply Fin.ext
  change (occupationAllocation b (compoundIndex d k i) t).val =
    (occupationAllocation b (compoundIndex d k j) t).val
  rw [← minorCoordinate_labelCount b i t, ← minorCoordinate_labelCount b j t]
  exact minor_counts_eq_of_nonzero_equal_weight b A hA
    (minorCoordinate d k i) (minorCoordinate d k j) hne heq' t

#print axioms sortedSubset_labelCount
#assert_trust kernel sortedSubset_labelCount
#print axioms compound_nonzero_occupation
#assert_trust kernel compound_nonzero_occupation

end NLA.MF06
