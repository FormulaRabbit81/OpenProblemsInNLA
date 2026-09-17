/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.
-/
import NLA.SP15.DerivativeRows.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section

theorem coefficient_strict_derivative_row_6 :
    HasStrictFDerivAt (fun x : Parameters => coefficients x 6)
      ((ContinuousLinearMap.proj (6 : Fin 9) : Coefficients →L[ℝ] ℝ).comp
        coefficientDerivative) basePoint := by
  have h (i : Fin 10) := hasStrictFDerivAt_apply (𝕜 := ℝ) i basePoint
  have hc := (((h 0).add (h 3)).add ((h 1).add (h 4))).add ((h 2).add (h 5))
  refine hc.congr_fderiv ?_
  ext v
  rw [coefficient_derivative_row_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  -- Both sides are the actual maps applied to an arbitrary perturbation vector.
  change ((v 0 + v 3) + (v 1 + v 4)) + (v 2 + v 5) =
    1 * v 0 + (1 * v 1 + (1 * v 2 + (1 * v 3 + (1 * v 4 +
      (1 * v 5 + (0 * v 6 + (0 * v 7 + (0 * v 8 + (0 * v 9 + 0)))))))))
  ring

#print axioms coefficient_strict_derivative_row_6
#assert_trust kernel coefficient_strict_derivative_row_6

end
end NLA.SP15
