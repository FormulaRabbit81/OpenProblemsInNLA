/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

Assemble all nine component strict derivatives, with all ten input coordinates.
-/
import NLA.SP15.DerivativeRows.Row0
import NLA.SP15.DerivativeRows.Row1
import NLA.SP15.DerivativeRows.Row2
import NLA.SP15.DerivativeRows.Row3
import NLA.SP15.DerivativeRows.Row4
import NLA.SP15.DerivativeRows.Row5
import NLA.SP15.DerivativeRows.Row6
import NLA.SP15.DerivativeRows.Row7
import NLA.SP15.DerivativeRows.Row8
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section

theorem coefficient_strict_derivative :
    HasStrictFDerivAt coefficients coefficientDerivative basePoint := by
  apply hasStrictFDerivAt_pi'.2
  intro i
  fin_cases i
  · exact coefficient_strict_derivative_row_0
  · exact coefficient_strict_derivative_row_1
  · exact coefficient_strict_derivative_row_2
  · exact coefficient_strict_derivative_row_3
  · exact coefficient_strict_derivative_row_4
  · exact coefficient_strict_derivative_row_5
  · exact coefficient_strict_derivative_row_6
  · exact coefficient_strict_derivative_row_7
  · exact coefficient_strict_derivative_row_8

#print axioms coefficient_strict_derivative
#assert_trust kernel coefficient_strict_derivative

end
end NLA.SP15
