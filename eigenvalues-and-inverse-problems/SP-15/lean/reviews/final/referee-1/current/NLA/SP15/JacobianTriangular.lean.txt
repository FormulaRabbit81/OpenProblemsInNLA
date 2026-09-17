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

theorem jacobian_lower_zero (i j : Fin 9) (hij : i < j) :
    lowerCertificate i j = 0 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl

theorem jacobian_lower_diag (i : Fin 9) : lowerCertificate i i = 1 := by
  fin_cases i <;> rfl

theorem jacobian_upper_zero (i j : Fin 9) (hij : j < i) :
    upperCertificate i j = 0 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl

theorem jacobian_upper_diag_ne (i : Fin 9) : upperCertificate i i ≠ 0 := by
  fin_cases i
  · -- Pivot 0 is definitionally the frozen rational entry.
    change (300 : ℝ) ≠ 0
    norm_num
  · -- Pivot 1 is definitionally the frozen rational entry.
    change (39 / 2 : ℝ) ≠ 0
    norm_num
  · -- Pivot 2 is definitionally the frozen rational entry.
    change (-100 / 39 : ℝ) ≠ 0
    norm_num
  · -- Pivot 3 is definitionally the frozen rational entry.
    change (37123 / 1875 : ℝ) ≠ 0
    norm_num
  · -- Pivot 4 is definitionally the frozen rational entry.
    change (345081 / 148492 : ℝ) ≠ 0
    norm_num
  · -- Pivot 5 is definitionally the frozen rational entry.
    change (-147294 / 115027 : ℝ) ≠ 0
    norm_num
  · -- Pivot 6 is definitionally the frozen rational entry.
    change (-1401 / 8183 : ℝ) ≠ 0
    norm_num
  · -- Pivot 7 is definitionally the frozen rational entry.
    change (4186 / 37827 : ℝ) ≠ 0
    norm_num
  · -- Pivot 8 is definitionally the frozen rational entry.
    change (136 / 2093 : ℝ) ≠ 0
    norm_num

theorem jacobian_upper_diag_product :
    (∏ i : Fin 9, upperCertificate i i) = (-1088 : ℝ) := by
  -- Left-to-right products keep every intermediate pivot product an integer.
  simp only [Fin.prod_univ_castSucc, Fin.prod_univ_zero]
  -- Each pivot lookup is checked against the actual frozen matrix.
  change ((((((((((1 * (300)) * (39 / 2)) * (-100 / 39)) * (37123 / 1875)) * (345081 / 148492)) * (-147294 / 115027)) * (-1401 / 8183)) * (4186 / 37827)) * (136 / 2093)) : ℝ) = -1088
  norm_num

#print axioms jacobian_lower_zero
#assert_trust kernel jacobian_lower_zero

#print axioms jacobian_lower_diag
#assert_trust kernel jacobian_lower_diag

#print axioms jacobian_upper_zero
#assert_trust kernel jacobian_upper_zero

#print axioms jacobian_upper_diag_ne
#assert_trust kernel jacobian_upper_diag_ne

#print axioms jacobian_upper_diag_product
#assert_trust kernel jacobian_upper_diag_product

end
end NLA.SP15
