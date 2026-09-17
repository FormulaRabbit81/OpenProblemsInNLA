/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

Row 7 of the frozen LU identity. Every typed change checks all nine actual
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

theorem jacobian_lu_row_7 (j : Fin 9) :
    jacobianMinor 7 j = (lowerCertificate * upperCertificate) 7 j := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases j
  · -- Column 0: retain every product; norm_num then removes zero terms.
    change (13 : ℝ) =
      ((13 / 300) * (300) + ((11 / 39) * (0) + ((-31 / 50) * (0) + ((90068 / 37123) * (0) + ((350762 / 345081) * (0) + ((-1217 / 73647) * (0) + ((198808 / 37827) * (0) + ((1) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 1: retain every product; norm_num then removes zero terms.
    change (12 : ℝ) =
      ((13 / 300) * (150) + ((11 / 39) * (39 / 2) + ((-31 / 50) * (0) + ((90068 / 37123) * (0) + ((350762 / 345081) * (0) + ((-1217 / 73647) * (0) + ((198808 / 37827) * (0) + ((1) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 2: retain every product; norm_num then removes zero terms.
    change (11 : ℝ) =
      ((13 / 300) * (100) + ((11 / 39) * (18) + ((-31 / 50) * (-100 / 39) + ((90068 / 37123) * (0) + ((350762 / 345081) * (0) + ((-1217 / 73647) * (0) + ((198808 / 37827) * (0) + ((1) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 3: retain every product; norm_num then removes zero terms.
    change (13 : ℝ) =
      ((13 / 300) * (84) + ((11 / 39) * (-1) + ((-31 / 50) * (20126 / 325) + ((90068 / 37123) * (37123 / 1875) + ((350762 / 345081) * (0) + ((-1217 / 73647) * (0) + ((198808 / 37827) * (0) + ((1) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 4: retain every product; norm_num then removes zero terms.
    change (12 : ℝ) =
      ((13 / 300) * (90) + ((11 / 39) * (19 / 2) + ((-31 / 50) * (1447 / 65) + ((90068 / 37123) * (2606 / 375) + ((350762 / 345081) * (345081 / 148492) + ((-1217 / 73647) * (0) + ((198808 / 37827) * (0) + ((1) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 5: retain every product; norm_num then removes zero terms.
    change (11 : ℝ) =
      ((13 / 300) * (90) + ((11 / 39) * (27 / 2) + ((-31 / 50) * (447 / 65) + ((90068 / 37123) * (327 / 125) + ((350762 / 345081) * (173535 / 148492) + ((-1217 / 73647) * (-147294 / 115027) + ((198808 / 37827) * (0) + ((1) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 6: retain every product; norm_num then removes zero terms.
    change (-2 : ℝ) =
      ((13 / 300) * (-36) + ((11 / 39) * (5) + ((-31 / 50) * (-11554 / 325) + ((90068 / 37123) * (-21392 / 1875) + ((350762 / 345081) * (335549 / 74246) + ((-1217 / 73647) * (-1983818 / 345081) + ((198808 / 37827) * (-1401 / 8183) + ((1) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 7: retain every product; norm_num then removes zero terms.
    change (-2 : ℝ) =
      ((13 / 300) * (-36) + ((11 / 39) * (3) + ((-31 / 50) * (-9054 / 325) + ((90068 / 37123) * (-5464 / 625) + ((350762 / 345081) * (131327 / 74246) + ((-1217 / 73647) * (-149846 / 345081) + ((198808 / 37827) * (1147 / 8183) + ((1) * (4186 / 37827) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 8: retain every product; norm_num then removes zero terms.
    change (-2 : ℝ) =
      ((13 / 300) * (-36) + ((11 / 39) * (-3) + ((-31 / 50) * (-1554 / 325) + ((90068 / 37123) * (-464 / 625) + ((350762 / 345081) * (-184355 / 74246) + ((-1217 / 73647) * (479654 / 345081) + ((198808 / 37827) * (369 / 1169) + ((1) * (1648 / 12609) + ((0) * (136 / 2093) + 0)))))))))
    norm_num

#print axioms jacobian_lu_row_7
#assert_trust kernel jacobian_lu_row_7

end
end NLA.SP15
