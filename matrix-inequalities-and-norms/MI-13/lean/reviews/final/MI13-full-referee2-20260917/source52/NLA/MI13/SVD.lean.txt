/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

Convert the proved singular-vector bases into an actual matrix SVD.
The construction includes zero dimension, repeated values and deficient rank.
-/
import NLA.MI13.NormalizedImages

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI13
noncomputable section
open scoped BigOperators Matrix

/-- Columns are the given orthonormal basis in the standard Euclidean coordinates. -/
def basisMatrix {r : ℕ} (v : OrthonormalBasis (Fin r) ℂ (EuclideanVector r)) :
    Square r := fun i j => v j i

theorem basisMatrix_eq_toMatrix {r : ℕ}
    (v : OrthonormalBasis (Fin r) ℂ (EuclideanVector r)) :
    basisMatrix v = (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.toMatrix v := by
  ext i j
  simp only [basisMatrix, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

theorem basisMatrix_unitary {r : ℕ}
    (v : OrthonormalBasis (Fin r) ℂ (EuclideanVector r)) : IsUnitary (basisMatrix v) := by
  rw [basisMatrix_eq_toMatrix]
  exact ⟨(EuclideanSpace.basisFun (Fin r) ℂ).toMatrix_orthonormalBasis_conjTranspose_mul_self v,
    (EuclideanSpace.basisFun (Fin r) ℂ).toMatrix_orthonormalBasis_self_mul_conjTranspose v⟩

theorem full_svd {r : ℕ} (A : Square r) :
    ∃ U V : Square r, IsUnitary U ∧ IsUnitary V ∧
      A = U * singularDiagonal A * V.conjTranspose := by
  obtain ⟨u, v, _, hAv⟩ := full_singular_vector_bases A
  have hU := basisMatrix_unitary u
  have hV := basisMatrix_unitary v
  have hAV : A * basisMatrix v = basisMatrix u * singularDiagonal A := by
    ext i j
    have h := congrArg (fun z : EuclideanVector r => z i) (hAv j)
    -- Coordinate evaluation unfolds the genuine Euclidean matrix action and
    -- its scalar multiplication to the same finite entry sum used by matrices.
    change (∑ k, A i k * v j k) = (singularValue A j.val : ℂ) * u j i at h
    calc
      (A * basisMatrix v) i j = ∑ k, A i k * v j k := rfl
      _ = (singularValue A j.val : ℂ) * u j i := h
      _ = (basisMatrix u * singularDiagonal A) i j := by
        simp only [singularDiagonal, Matrix.mul_diagonal, basisMatrix, mul_comm]
  refine ⟨basisMatrix u, basisMatrix v, hU, hV, ?_⟩
  calc
    A = A * (basisMatrix v * (basisMatrix v).conjTranspose) := by
      rw [hV.2, Matrix.mul_one]
    _ = (A * basisMatrix v) * (basisMatrix v).conjTranspose :=
      (Matrix.mul_assoc _ _ _).symm
    _ = basisMatrix u * singularDiagonal A * (basisMatrix v).conjTranspose := by
      rw [hAV]

#print axioms full_svd
#assert_trust kernel full_svd

end
end NLA.MI13
