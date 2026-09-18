/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The literal sorted minors are the matrix of the genuine exterior-power map.
Mathlib's exterior basis and dual-coordinate construction retain their authorship.
The dual-coordinate determinant is transposed, with no additional sign. Matrix
functoriality then proves composition, including degree zero and degrees beyond
the dimension. No determinant or subset enumeration is evaluated numerically.
-/
import NLA.MF06.Definitions

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07
open scoped Matrix

theorem compound_dimensions (d k : ℕ) :
    compoundDim d k = Nat.choose d k ∧ (k ≤ d → 1 ≤ compoundDim d k) := by
  have hcard : compoundDim d k = Nat.choose d k := by
    unfold compoundDim ExteriorIndex
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card]
    simp
  refine ⟨hcard, ?_⟩
  intro hk
  rw [hcard]
  exact Nat.choose_pos hk

theorem compound_coordinate_semantics {d : ℕ} (k : ℕ) (A : Square d)
    (i j : Fin (compoundDim d k)) :
    compoundMatrix k A i j =
      ((Pi.basisFun ℂ (Fin d)).exteriorPower k).repr
        (exteriorPower.map k (Matrix.toLin' A)
          (((Pi.basisFun ℂ (Fin d)).exteriorPower k) (compoundIndex d k j)))
        (compoundIndex d k i) := by
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family]
  unfold exteriorPower.ιMulti_family
  rw [exteriorPower.ιMultiDual_apply_ιMulti]
  have hmatrix :
      (Matrix.of fun a b : Fin k =>
        (Pi.basisFun ℂ (Fin d)).coord (minorCoordinate d k i b)
          ((Matrix.toLin' A) ((Pi.basisFun ℂ (Fin d)) (minorCoordinate d k j a)))) =
      (A.submatrix (minorCoordinate d k i) (minorCoordinate d k j))ᵀ := by
    ext a b
    simp only [Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr,
      Matrix.toLin'_apply, Pi.basisFun_apply, Matrix.mulVec_single_one,
      Matrix.col_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
  -- Expand the frozen literal minor and exterior dual determinant. The dual
  -- uses transposed row/column indices, removed by det_transpose below.
  change Matrix.det (A.submatrix (minorCoordinate d k i) (minorCoordinate d k j)) = _
  change _ = Matrix.det (Matrix.of fun a b : Fin k =>
    (Pi.basisFun ℂ (Fin d)).coord (minorCoordinate d k i b)
      ((Matrix.toLin' A) ((Pi.basisFun ℂ (Fin d)) (minorCoordinate d k j a))))
  rw [hmatrix, Matrix.det_transpose]

/-- The standard exterior basis with exactly the frozen finite coordinate order. -/
def compoundBasis (d k : ℕ) :
    Module.Basis (Fin (compoundDim d k)) ℂ (⋀[ℂ]^k (Fin d → ℂ)) :=
  ((Pi.basisFun ℂ (Fin d)).exteriorPower k).reindex
    (Fintype.equivFin (ExteriorIndex d k))

lemma compoundMatrix_eq_toMatrix {d : ℕ} (k : ℕ) (A : Square d) :
    compoundMatrix k A = LinearMap.toMatrix (compoundBasis d k) (compoundBasis d k)
      (exteriorPower.map k (Matrix.toLin' A)) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  dsimp only [compoundBasis]
  erw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  exact compound_coordinate_semantics k A i j

theorem compound_algebra {d : ℕ} (k : ℕ) (A B : Square d) :
    compoundMatrix k (1 : Square d) = 1 ∧
    compoundMatrix k (A * B) = compoundMatrix k A * compoundMatrix k B ∧
    compoundMatrix 0 A = 1 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [compoundMatrix_eq_toMatrix, Matrix.toLin'_one, exteriorPower.map_id,
      LinearMap.toMatrix_id]
  · rw [compoundMatrix_eq_toMatrix, Matrix.toLin'_mul, exteriorPower.map_comp,
      LinearMap.toMatrix_comp (compoundBasis d k) (compoundBasis d k) (compoundBasis d k),
      ← compoundMatrix_eq_toMatrix, ← compoundMatrix_eq_toMatrix]
  · have hdim : compoundDim d 0 = 1 := by rw [(compound_dimensions d 0).1]; simp
    ext i j
    have hij : i = j := by
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      omega
    subst j
    simp [compoundMatrix]

#print axioms compound_dimensions
#assert_trust kernel compound_dimensions
#print axioms compound_coordinate_semantics
#assert_trust kernel compound_coordinate_semantics
#print axioms compound_algebra
#assert_trust kernel compound_algebra

end NLA.MF06
