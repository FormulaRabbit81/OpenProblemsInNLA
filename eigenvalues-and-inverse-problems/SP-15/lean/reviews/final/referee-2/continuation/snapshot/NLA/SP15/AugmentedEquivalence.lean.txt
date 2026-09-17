/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

One nonzero last-row term reduces the augmented determinant to the previously
certified minor. The matrix-to-map bridge uses the actual frozen CLM wrapper.
-/
import NLA.SP15.AugmentedDerivative
import NLA.SP15.JacobianCertificate
import Mathlib.LinearAlgebra.Determinant

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped BigOperators Matrix

private theorem augmented_jacobian_last_row (j : Fin 10) :
    augmentedJacobian (Fin.last 9) j = if j = (9 : Fin 10) then 1 else 0 := by
  exact congrFun augmented_jacobian_final_row j

private theorem augmented_jacobian_last_minor :
    augmentedJacobian.submatrix (Fin.last 9).succAbove (Fin.last 9).succAbove =
      jacobianMinor := by
  ext i j
  simp only [Matrix.submatrix_apply, Fin.succAbove_last, jacobianMinor]
  exact congrFun (augmented_jacobian_initial_row i) j.castSucc

private theorem augmented_jacobian_determinant :
    augmentedJacobian.det = (-1088 : ℝ) := by
  have hreduce : augmentedJacobian.det = jacobianMinor.det := by
    rw [Matrix.det_succ_row augmentedJacobian (Fin.last 9)]
    rw [Finset.sum_eq_single (Fin.last 9)]
    · -- Fin.last 9 is definitionally the literal last index (9 : Fin 10) in this row.
      rw [augmented_jacobian_last_minor, augmented_jacobian_last_row,
        if_pos (show Fin.last 9 = (9 : Fin 10) from rfl)]
      norm_num
    · intro j _ hj
      rw [augmented_jacobian_last_row]
      have hj' : j ≠ (9 : Fin 10) := hj
      simp only [if_neg hj', mul_zero, zero_mul]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  exact hreduce.trans jacobian_minor_nonsingular

theorem augmented_derivative_equivalence :
    ∃ e : Parameters ≃L[ℝ] Parameters,
      (e : Parameters →L[ℝ] Parameters) = augmentedDerivative := by
  have hdet : augmentedDerivative.det ≠ 0 := by
    -- The continuous wrapper and Matrix.toLin' have the same actual linear map.
    change LinearMap.det (Matrix.toLin' augmentedJacobian) ≠ 0
    rw [LinearMap.det_toLin', augmented_jacobian_determinant]
    norm_num
  exact ⟨augmentedDerivative.toContinuousLinearEquivOfDetNeZero hdet,
    augmentedDerivative.coe_toContinuousLinearEquivOfDetNeZero hdet⟩

#print axioms augmented_derivative_equivalence
#assert_trust kernel augmented_derivative_equivalence

end
end NLA.SP15
