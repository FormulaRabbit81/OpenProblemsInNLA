/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

The augmented derivative uses the actual nine coefficient rows and the actual
free-coordinate projection. No Jacobian entries are recalculated or assumed.
-/
import NLA.SP15.CoefficientDerivative

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped BigOperators

theorem augmented_jacobian_initial_row (i : Fin 9) :
    augmentedJacobian i.castSucc = jacobian i := by
  exact Fin.lastCases_castSucc (n := 9) (motive := fun _ : Fin 10 => Fin 10 → ℝ)
    (last := fun j : Fin 10 => if j = 9 then (1 : ℝ) else 0) (cast := jacobian) i

theorem augmented_jacobian_final_row :
    augmentedJacobian (Fin.last 9) = fun j : Fin 10 => if j = 9 then (1 : ℝ) else 0 := by
  exact Fin.lastCases_last (n := 9) (motive := fun _ : Fin 10 => Fin 10 → ℝ)
    (last := fun j : Fin 10 => if j = 9 then (1 : ℝ) else 0) (cast := jacobian)

private theorem augmented_derivative_initial (v : Parameters) (i : Fin 9) :
    augmentedDerivative v i.castSucc = coefficientDerivative v i := by
  -- Expose the frozen continuous matrix maps at coordinate i before rewriting its row.
  change (∑ j : Fin 10, augmentedJacobian i.castSucc j * v j) =
    ∑ j : Fin 10, jacobian i j * v j
  rw [augmented_jacobian_initial_row]

private theorem augmented_derivative_last (v : Parameters) :
    augmentedDerivative v (Fin.last 9) = v 9 := by
  -- The last coordinate of the same matrix action is its literal final-row sum.
  change (∑ j : Fin 10, augmentedJacobian (Fin.last 9) j * v j) = v 9
  rw [augmented_jacobian_final_row]
  simp [ite_mul]

private theorem augmented_initial_map (i : Fin 9) :
    (ContinuousLinearMap.proj i.castSucc : Parameters →L[ℝ] ℝ).comp augmentedDerivative =
      (ContinuousLinearMap.proj i : Coefficients →L[ℝ] ℝ).comp coefficientDerivative := by
  ext v
  exact augmented_derivative_initial v i

private theorem augmented_last_map :
    (ContinuousLinearMap.proj (Fin.last 9) : Parameters →L[ℝ] ℝ).comp augmentedDerivative =
      (ContinuousLinearMap.proj (9 : Fin 10) : Parameters →L[ℝ] ℝ) := by
  ext v
  exact augmented_derivative_last v

theorem augmented_strict_derivative :
    HasStrictFDerivAt augmented augmentedDerivative basePoint := by
  apply hasStrictFDerivAt_pi'.2
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [augmented_last_map]
    simpa only [augmented, Fin.lastCases_last] using
      (hasStrictFDerivAt_apply (𝕜 := ℝ) (9 : Fin 10) basePoint)
  · rw [augmented_initial_map]
    simpa only [augmented, Fin.lastCases_castSucc] using
      (hasStrictFDerivAt_pi'.1 coefficient_strict_derivative j)

#print axioms augmented_strict_derivative
#assert_trust kernel augmented_strict_derivative

end
end NLA.SP15
