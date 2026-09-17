/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

Row 5 of the frozen LU identity. Every typed change checks all nine actual
table entries by definitional equality before sparse rational arithmetic.
No untrusted numerical output is imported as a premise.
-/
import NLA.SP15.Numerical
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped BigOperators Matrix

theorem jacobian_lu_row_5 (j : Fin 9) :
    jacobianMinor 5 j = (lowerCertificate * upperCertificate) 5 j := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases j
  · -- Column 0: retain every product; norm_num then removes zero terms.
    change (267 : ℝ) =
      ((89 / 100) * (300) + ((11 / 3) * (0) + ((-78 / 25) * (0) + ((525218 / 37123) * (0) + ((1218104 / 345081) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 1: retain every product; norm_num then removes zero terms.
    change (205 : ℝ) =
      ((89 / 100) * (150) + ((11 / 3) * (39 / 2) + ((-78 / 25) * (0) + ((525218 / 37123) * (0) + ((1218104 / 345081) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 2: retain every product; norm_num then removes zero terms.
    change (163 : ℝ) =
      ((89 / 100) * (100) + ((11 / 3) * (18) + ((-78 / 25) * (-100 / 39) + ((525218 / 37123) * (0) + ((1218104 / 345081) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 3: retain every product; norm_num then removes zero terms.
    change (158 : ℝ) =
      ((89 / 100) * (84) + ((11 / 3) * (-1) + ((-78 / 25) * (20126 / 325) + ((525218 / 37123) * (37123 / 1875) + ((1218104 / 345081) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 4: retain every product; norm_num then removes zero terms.
    change (152 : ℝ) =
      ((89 / 100) * (90) + ((11 / 3) * (19 / 2) + ((-78 / 25) * (1447 / 65) + ((525218 / 37123) * (2606 / 375) + ((1218104 / 345081) * (345081 / 148492) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 5: retain every product; norm_num then removes zero terms.
    change (148 : ℝ) =
      ((89 / 100) * (90) + ((11 / 3) * (27 / 2) + ((-78 / 25) * (447 / 65) + ((525218 / 37123) * (327 / 125) + ((1218104 / 345081) * (173535 / 148492) + ((1) * (-147294 / 115027) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 6: retain every product; norm_num then removes zero terms.
    change (-54 : ℝ) =
      ((89 / 100) * (-36) + ((11 / 3) * (5) + ((-78 / 25) * (-11554 / 325) + ((525218 / 37123) * (-21392 / 1875) + ((1218104 / 345081) * (335549 / 74246) + ((1) * (-1983818 / 345081) + ((0) * (-1401 / 8183) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 7: retain every product; norm_num then removes zero terms.
    change (-52 : ℝ) =
      ((89 / 100) * (-36) + ((11 / 3) * (3) + ((-78 / 25) * (-9054 / 325) + ((525218 / 37123) * (-5464 / 625) + ((1218104 / 345081) * (131327 / 74246) + ((1) * (-149846 / 345081) + ((0) * (1147 / 8183) + ((0) * (4186 / 37827) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 8: retain every product; norm_num then removes zero terms.
    change (-46 : ℝ) =
      ((89 / 100) * (-36) + ((11 / 3) * (-3) + ((-78 / 25) * (-1554 / 325) + ((525218 / 37123) * (-464 / 625) + ((1218104 / 345081) * (-184355 / 74246) + ((1) * (479654 / 345081) + ((0) * (369 / 1169) + ((0) * (1648 / 12609) + ((0) * (136 / 2093) + 0)))))))))
    norm_num

#print axioms jacobian_lu_row_5
#assert_trust kernel jacobian_lu_row_5

end
end NLA.SP15
