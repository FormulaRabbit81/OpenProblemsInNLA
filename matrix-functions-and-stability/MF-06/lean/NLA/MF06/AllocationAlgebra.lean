/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Finite products of entries define the actual tensor-coordinate matrix. The
product-of-sums identity proves multiplication symbolically. Reindexing by the
frozen allocation coordinates retains every component and its original order.
-/
import NLA.MF06.AllocationDimensions
import NLA.MF06.BlockAlgebra

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

def coordinateTensor {ι : Type*} [Fintype ι] {n : ι → ℕ}
    (A : ∀ i, Square (n i)) : Matrix (∀ i, Fin (n i)) (∀ i, Fin (n i)) ℂ :=
  fun u v => ∏ i, A i (u i) (v i)

lemma coordinateTensor_one {ι : Type*} [Fintype ι] {n : ι → ℕ} :
    coordinateTensor (fun i => (1 : Square (n i))) = 1 := by
  classical
  ext u v
  by_cases h : u = v
  · subst v
    simp [coordinateTensor]
  · rw [Matrix.one_apply, if_neg h]
    have hcoord : ∃ i, u i ≠ v i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    obtain ⟨i, hi⟩ := hcoord
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [Matrix.one_apply, if_neg hi])

lemma coordinateTensor_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (A B : ∀ i, Square (n i)) :
    coordinateTensor (fun i => A i * B i) = coordinateTensor A * coordinateTensor B := by
  classical
  ext u v
  simp only [coordinateTensor, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl (fun j _ => Finset.prod_mul_distrib)

lemma allocationCoordinate_injective {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b) :
    Function.Injective (allocationCoordinate b a) :=
  (Fintype.equivFin (AllocationIndex b a)).symm.injective

/-- The same frozen allocation coordinates, applied to an arbitrary tuple of
actual diagonal-size matrices. No triangularity is needed for this tensor map. -/
def allocationTensor {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (P : ∀ i : Fin r, Square (blockDim b i)) : Square (allocationDim b a) :=
  (coordinateTensor (fun i => compoundMatrix (a i).val (P i))).submatrix
    (allocationCoordinate b a) (allocationCoordinate b a)

lemma allocationTensor_one {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b) :
    allocationTensor b a (fun i => (1 : Square (blockDim b i))) = 1 := by
  unfold allocationTensor
  have h : (fun i => compoundMatrix (a i).val (1 : Square (blockDim b i))) =
      (fun i => (1 : Square (compoundDim (blockDim b i) (a i).val))) := by
    funext i
    exact (compound_algebra (a i).val (1 : Square (blockDim b i)) 1).1
  rw [h, coordinateTensor_one]
  exact Matrix.submatrix_one _ (allocationCoordinate_injective b a)

lemma allocationTensor_mul {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (P Q : ∀ i : Fin r, Square (blockDim b i)) :
    allocationTensor b a (fun i => P i * Q i) = allocationTensor b a P * allocationTensor b a Q := by
  unfold allocationTensor
  have h : (fun i => compoundMatrix (a i).val (P i * Q i)) =
      (fun i => compoundMatrix (a i).val (P i) * compoundMatrix (a i).val (Q i)) := by
    funext i
    exact (compound_algebra (a i).val (P i) (Q i)).2.1
  rw [h, coordinateTensor_mul]
  exact Matrix.submatrix_mul _ _ _ _ _ (Fintype.equivFin (AllocationIndex b a)).symm.bijective

lemma allocationMatrix_eq_allocationTensor {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (A : Square d) : allocationMatrix b a A = allocationTensor b a (fun i => blockMatrix b i A) := rfl

theorem allocation_algebra {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (A B : Square d) (hA : IsUpperBlockTriangular b A) (hB : IsUpperBlockTriangular b B) :
    allocationMatrix b a (1 : Square d) = 1 ∧
    allocationMatrix b a (A * B) = allocationMatrix b a A * allocationMatrix b a B := by
  constructor
  · simpa only [allocationMatrix_eq_allocationTensor, blockMatrix_one] using allocationTensor_one b a
  · have h : (fun i : Fin r => blockMatrix b i (A * B)) =
        (fun i => blockMatrix b i A * blockMatrix b i B) := by
      funext i
      exact blockMatrix_mul b i A B hA hB
    change allocationTensor b a (fun i => blockMatrix b i (A * B)) =
      allocationTensor b a (fun i => blockMatrix b i A) * allocationTensor b a (fun i => blockMatrix b i B)
    rw [h, allocationTensor_mul]

#print axioms allocation_algebra
#assert_trust kernel allocation_algebra

end NLA.MF06
