/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Flag membership is expressed by actual vanishing basis coefficients. The
block projection is a concrete linear map into the frozen fiber coordinates.
Its intertwining relation on a prefix proves the later quotient action.
-/
import NLA.MF06.FlagMatrices
import NLA.MF06.BlockCoordinates

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma mem_flag_iff_repr_zero {d r : ℕ}
    (F : Fin (r + 1) → Submodule ℂ (EuclideanVector d))
    (B : Module.Basis (Fin d) ℂ (EuclideanVector d)) (b : Fin d → Fin r)
    (hspan : ∀ i, Submodule.span ℂ (B '' {j | (b j).val < i.val}) = F i)
    (i : Fin (r + 1)) (x : EuclideanVector d) :
    x ∈ F i ↔ ∀ j, i.val ≤ (b j).val → B.repr x j = 0 := by
  rw [← hspan i, B.mem_span_image]
  constructor
  · intro h j hj
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have hlt : (b j).val < i.val := h hmem
    omega
  · intro h j hj
    change (b j).val < i.val
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hj) (h j (by omega))

def flagBlockProjection {d r : ℕ}
    (B : Module.Basis (Fin d) ℂ (EuclideanVector d)) (b : Fin d → Fin r) (i : Fin r) :
    EuclideanVector d →ₗ[ℂ] EuclideanVector (blockDim b i) :=
  ((WithLp.linearEquiv 2 ℂ (Fin (blockDim b i) → ℂ)).symm.toLinearMap).comp
    (LinearMap.pi (fun u => B.coord (blockCoordinate b i u)))

lemma flagBlockProjection_apply {d r : ℕ}
    (B : Module.Basis (Fin d) ℂ (EuclideanVector d)) (b : Fin d → Fin r) (i : Fin r)
    (x : EuclideanVector d) (u : Fin (blockDim b i)) :
    flagBlockProjection B b i x u = B.repr x (blockCoordinate b i u) := rfl

lemma repr_applyMatrix {d : ℕ} (B : Module.Basis (Fin d) ℂ (EuclideanVector d))
    (A : Square d) (x : EuclideanVector d) (j : Fin d) :
    B.repr (applyMatrix A x) j = ∑ k, inBasis B A j k * B.repr x k := by
  have h := LinearMap.toMatrix_mulVec_repr B B (Matrix.toEuclideanLin A) x
  exact (congrFun h j).symm

lemma flagBlockProjection_action {d r : ℕ}
    (F : Fin (r + 1) → Submodule ℂ (EuclideanVector d))
    (B : Module.Basis (Fin d) ℂ (EuclideanVector d)) (b : Fin d → Fin r)
    (hspan : ∀ i, Submodule.span ℂ (B '' {j | (b j).val < i.val}) = F i)
    (A : Square d) (hupper : IsUpperBlockTriangular b (inBasis B A))
    (i : Fin r) (x : EuclideanVector d) (hx : x ∈ F i.succ) :
    flagBlockProjection B b i (applyMatrix A x) =
      applyMatrix (blockMatrix b i (inBasis B A)) (flagBlockProjection B b i x) := by
  ext u
  rw [flagBlockProjection_apply, repr_applyMatrix]
  have hzero (j : Fin d) (hj : b j ≠ i) :
      inBasis B A (blockCoordinate b i u) j * B.repr x j = 0 := by
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hupper _ _ (by rwa [blockCoordinate_label b i u]), zero_mul]
    · have hxj := (mem_flag_iff_repr_zero F B b hspan i.succ x).mp hx j
        (show i.val + 1 ≤ (b j).val from h)
      rw [hxj, mul_zero]
  rw [blockCoordinate_sum b i _ hzero]
  rfl

#print axioms mem_flag_iff_repr_zero
#assert_trust kernel mem_flag_iff_repr_zero
#print axioms flagBlockProjection_action
#assert_trust kernel flagBlockProjection_action

end NLA.MF06
