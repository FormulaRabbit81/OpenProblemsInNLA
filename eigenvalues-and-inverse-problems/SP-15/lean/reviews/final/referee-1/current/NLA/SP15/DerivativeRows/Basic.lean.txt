/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

Expose the actual continuous-linear-map wrapper of the frozen full Jacobian.
This is an equality of maps applied to arbitrary vectors, not sampled data.
-/
import NLA.SP15.Numerical
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped BigOperators

theorem coefficient_derivative_row_apply (i : Fin 9) (v : Parameters) :
    ((ContinuousLinearMap.proj i : Coefficients →L[ℝ] ℝ).comp coefficientDerivative) v =
      ∑ j : Fin 10, jacobian i j * v j := by
  rfl

#print axioms coefficient_derivative_row_apply
#assert_trust kernel coefficient_derivative_row_apply

end
end NLA.SP15
