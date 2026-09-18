/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

A coordinate map landing in a known original fiber factors through its frozen
enumeration. This is an explicit submatrix identity, independent of dimensions,
invertibility, or any matrix norm assumption.
-/
import NLA.MF06.BlockCoordinates
import NLA.MF06.ImageWordComparison
import NLA.MF06.TensorAlgebra

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

def fiberCoordinate {d r m : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (e : Fin m → Fin d) (he : ∀ u, b (e u) = i) (u : Fin m) : Fin (blockDim b i) :=
  Fintype.equivFin (BlockIndex b i) ⟨e u, he u⟩

lemma blockCoordinate_fiberCoordinate {d r m : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (e : Fin m → Fin d) (he : ∀ u, b (e u) = i) (u : Fin m) :
    blockCoordinate b i (fiberCoordinate b i e he u) = e u :=
  congrArg Subtype.val ((Fintype.equivFin (BlockIndex b i)).symm_apply_apply ⟨e u, he u⟩)

lemma submatrix_eq_block_submatrix {d r m : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (e : Fin m → Fin d) (he : ∀ u, b (e u) = i) (A : Square d) :
    A.submatrix e e = (blockMatrix b i A).submatrix
      (fiberCoordinate b i e he) (fiberCoordinate b i e he) := by
  ext u v
  change A (e u) (e v) = A (blockCoordinate b i (fiberCoordinate b i e he u))
    (blockCoordinate b i (fiberCoordinate b i e he v))
  rw [blockCoordinate_fiberCoordinate, blockCoordinate_fiberCoordinate]

lemma spectralNorm_submatrix_fiber_le {d r m : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (e : Fin m → Fin d) (he : ∀ u, b (e u) = i) (A : Square d) :
    spectralNorm (A.submatrix e e) ≤ (m : ℝ) * spectralNorm (blockMatrix b i A) := by
  rw [submatrix_eq_block_submatrix b i e he A]
  exact spectralNorm_submatrix_le _ _

/-- The product-coordinate map follows the frozen tensor reindexing. -/
def tensorCoordinateMap {m n p q : ℕ} (e : Fin m → Fin p) (f : Fin n → Fin q)
    (u : Fin (m * n)) : Fin (p * q) :=
  finProdFinEquiv (e ((finProdFinEquiv (m := m) (n := n)).symm u).1,
    f ((finProdFinEquiv (m := m) (n := n)).symm u).2)

lemma tensor_submatrix_eq {m n p q : ℕ} (A : Square p) (B : Square q)
    (e : Fin m → Fin p) (f : Fin n → Fin q) :
    tensorMatrix (A.submatrix e e) (B.submatrix f f) =
      (tensorMatrix A B).submatrix (tensorCoordinateMap e f) (tensorCoordinateMap e f) := by
  ext u v
  simp only [tensorMatrix, Matrix.kronecker, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, tensorCoordinateMap, Equiv.symm_apply_apply]

lemma spectralNorm_tensor_submatrix_le {m n p q : ℕ} (A : Square p) (B : Square q)
    (e : Fin m → Fin p) (f : Fin n → Fin q) :
    spectralNorm (tensorMatrix (A.submatrix e e) (B.submatrix f f)) ≤
      ((m * n : ℕ) : ℝ) * spectralNorm (tensorMatrix A B) := by
  rw [tensor_submatrix_eq]
  exact spectralNorm_submatrix_le _ _

#print axioms spectralNorm_submatrix_fiber_le
#assert_trust kernel spectralNorm_submatrix_fiber_le
#print axioms spectralNorm_tensor_submatrix_le
#assert_trust kernel spectralNorm_tensor_submatrix_le

end NLA.MF06
