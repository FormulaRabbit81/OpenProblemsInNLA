/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

All 81 actual entry identities come from the separately checked row modules.
Triangular determinants use nine pivots; the 9×9 determinant is never expanded.
Identification with the actual coefficient derivative is a later obligation.
-/
import NLA.SP15.CoefficientValue
import NLA.SP15.JacobianTriangular
import NLA.SP15.JacobianRows.Row0
import NLA.SP15.JacobianRows.Row1
import NLA.SP15.JacobianRows.Row2
import NLA.SP15.JacobianRows.Row3
import NLA.SP15.JacobianRows.Row4
import NLA.SP15.JacobianRows.Row5
import NLA.SP15.JacobianRows.Row6
import NLA.SP15.JacobianRows.Row7
import NLA.SP15.JacobianRows.Row8
import Mathlib.LinearAlgebra.Matrix.Block

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped BigOperators Matrix

theorem jacobian_lu_certificate :
    jacobianMinor = lowerCertificate * upperCertificate ∧
    (∀ i j : Fin 9, i < j → lowerCertificate i j = 0) ∧
    (∀ i : Fin 9, lowerCertificate i i = 1) ∧
    (∀ i j : Fin 9, j < i → upperCertificate i j = 0) ∧
    (∀ i : Fin 9, upperCertificate i i ≠ 0) ∧
    (∏ i : Fin 9, upperCertificate i i) = (-1088 : ℝ) := by
  refine ⟨?_, jacobian_lower_zero, jacobian_lower_diag, jacobian_upper_zero,
    jacobian_upper_diag_ne, jacobian_upper_diag_product⟩
  ext i j
  fin_cases i
  · exact jacobian_lu_row_0 j
  · exact jacobian_lu_row_1 j
  · exact jacobian_lu_row_2 j
  · exact jacobian_lu_row_3 j
  · exact jacobian_lu_row_4 j
  · exact jacobian_lu_row_5 j
  · exact jacobian_lu_row_6 j
  · exact jacobian_lu_row_7 j
  · exact jacobian_lu_row_8 j

theorem jacobian_minor_nonsingular : jacobianMinor.det = (-1088 : ℝ) := by
  obtain ⟨hreconstruct, hLower, hLowerDiag, hUpper, _, hProduct⟩ := jacobian_lu_certificate
  have hL : lowerCertificate.IsLowerTriangular := by
    intro i j hij
    exact hLower i j hij
  have hU : upperCertificate.IsUpperTriangular := by
    intro i j hij
    exact hUpper i j hij
  rw [hreconstruct, Matrix.det_mul, Matrix.det_of_isLowerTriangular lowerCertificate hL,
    Matrix.det_of_isUpperTriangular hU, hProduct]
  simp [hLowerDiag]

#print axioms jacobian_lu_certificate
#assert_trust kernel jacobian_lu_certificate
#print axioms jacobian_minor_nonsingular
#assert_trust kernel jacobian_minor_nonsingular

end
end NLA.SP15
