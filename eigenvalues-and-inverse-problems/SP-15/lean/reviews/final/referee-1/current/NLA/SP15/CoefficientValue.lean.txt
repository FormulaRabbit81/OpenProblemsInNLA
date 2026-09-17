/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.
-/
import NLA.SP15.Numerical
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped BigOperators Matrix

theorem coefficient_base_value : coefficients basePoint = coefficientBaseValue := by
  funext i
  fin_cases i
  · -- Coordinate 0: expose the actual frozen polynomial and base-point entries.
    change ((((((((1 * 4) * (2 * 4)) * (3 * 4)) - (((((1 ^ 2) + (1 ^ 2)) * 2) * 3) * (1 * 4))) - ((((1 ^ 2) * 1) * 3) * (2 * 4))) - ((((1 ^ 2) * 1) * 2) * (3 * 4))) + ((((((2 * 1) * 1) * 1) * 1) * 2) * 3)) : ℝ) = (300 : ℝ)
    norm_num
  · -- Coordinate 1: expose the actual frozen polynomial and base-point entries.
    change ((((((((1 * 4) * (2 * 4)) + ((1 * 4) * (3 * 4))) + ((2 * 4) * (3 * 4))) - ((((1 ^ 2) + (1 ^ 2)) * 2) * 3)) - (((1 ^ 2) * 1) * 3)) - (((1 ^ 2) * 1) * 2)) : ℝ) = (159 : ℝ)
    norm_num
  · -- Coordinate 2: expose the actual frozen polynomial and base-point entries.
    change ((((((((((1 + 4) * (2 * 4)) * (3 * 4)) + (((1 * 4) * (2 + 4)) * (3 * 4))) + (((1 * 4) * (2 * 4)) * (3 + 4))) - (((1 ^ 2) + (1 ^ 2)) * (((2 * 3) * (1 + 4)) + ((2 + 3) * (1 * 4))))) - ((1 ^ 2) * (((1 * 3) * (2 + 4)) + ((1 + 3) * (2 * 4))))) - ((1 ^ 2) * (((1 * 2) * (3 + 4)) + ((1 + 2) * (3 * 4))))) + ((((2 * 1) * 1) * 1) * (((1 * 2) + (1 * 3)) + (2 * 3)))) : ℝ) = (814 : ℝ)
    norm_num
  · -- Coordinate 3: expose the actual frozen polynomial and base-point entries.
    change ((((1 * 4) + (2 * 4)) + (3 * 4)) : ℝ) = (24 : ℝ)
    norm_num
  · -- Coordinate 4: expose the actual frozen polynomial and base-point entries.
    change (((((((((((1 + 4) * (2 * 4)) + ((1 * 4) * (2 + 4))) + ((1 + 4) * (3 * 4))) + ((1 * 4) * (3 + 4))) + ((2 + 4) * (3 * 4))) + ((2 * 4) * (3 + 4))) - (((1 ^ 2) + (1 ^ 2)) * (2 + 3))) - ((1 ^ 2) * (1 + 3))) - ((1 ^ 2) * (1 + 2))) : ℝ) = (263 : ℝ)
    norm_num
  · -- Coordinate 5: expose the actual frozen polynomial and base-point entries.
    change ((((((((((1 + 4) * (2 + 4)) * (3 * 4)) + (((1 + 4) * (2 * 4)) * (3 + 4))) + (((1 * 4) * (2 + 4)) * (3 + 4))) - (((1 ^ 2) + (1 ^ 2)) * (((2 + 3) * (1 + 4)) + (1 * 4)))) - ((1 ^ 2) * (((1 + 3) * (2 + 4)) + (2 * 4)))) - ((1 ^ 2) * (((1 + 2) * (3 + 4)) + (3 * 4)))) + ((((2 * 1) * 1) * 1) * ((1 + 2) + 3))) : ℝ) = (697 : ℝ)
    norm_num
  · -- Coordinate 6: expose the actual frozen polynomial and base-point entries.
    change ((((1 + 4) + (2 + 4)) + (3 + 4)) : ℝ) = (18 : ℝ)
    norm_num
  · -- Coordinate 7: expose the actual frozen polynomial and base-point entries.
    change ((((((((1 + 4) * (2 + 4)) + ((1 + 4) * (3 + 4))) + ((2 + 4) * (3 + 4))) - ((1 ^ 2) + (1 ^ 2))) - (1 ^ 2)) - (1 ^ 2)) : ℝ) = (103 : ℝ)
    norm_num
  · -- Coordinate 8: expose the actual frozen polynomial and base-point entries.
    change ((((((((1 + 4) * (2 + 4)) * (3 + 4)) - (((1 ^ 2) + (1 ^ 2)) * (1 + 4))) - ((1 ^ 2) * (2 + 4))) - ((1 ^ 2) * (3 + 4))) + (((2 * 1) * 1) * 1)) : ℝ) = (189 : ℝ)
    norm_num

#print axioms coefficient_base_value
#assert_trust kernel coefficient_base_value

end
end NLA.SP15
