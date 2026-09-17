/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

Row 4 of the frozen LU identity. Every typed change checks all nine actual
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

theorem jacobian_lu_row_4 (j : Fin 9) :
    jacobianMinor 4 j = (lowerCertificate * upperCertificate) 4 j := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases j
  · -- Column 0: retain every product; norm_num then removes zero terms.
    change (70 : ℝ) =
      ((7 / 30) * (300) + ((4 / 3) * (0) + ((-221 / 100) * (0) + ((568463 / 74246) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 1: retain every product; norm_num then removes zero terms.
    change (61 : ℝ) =
      ((7 / 30) * (150) + ((4 / 3) * (39 / 2) + ((-221 / 100) * (0) + ((568463 / 74246) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 2: retain every product; norm_num then removes zero terms.
    change (53 : ℝ) =
      ((7 / 30) * (100) + ((4 / 3) * (18) + ((-221 / 100) * (-100 / 39) + ((568463 / 74246) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 3: retain every product; norm_num then removes zero terms.
    change (33 : ℝ) =
      ((7 / 30) * (84) + ((4 / 3) * (-1) + ((-221 / 100) * (20126 / 325) + ((568463 / 74246) * (37123 / 1875) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 4: retain every product; norm_num then removes zero terms.
    change (40 : ℝ) =
      ((7 / 30) * (90) + ((4 / 3) * (19 / 2) + ((-221 / 100) * (1447 / 65) + ((568463 / 74246) * (2606 / 375) + ((1) * (345081 / 148492) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 5: retain every product; norm_num then removes zero terms.
    change (45 : ℝ) =
      ((7 / 30) * (90) + ((4 / 3) * (27 / 2) + ((-221 / 100) * (447 / 65) + ((568463 / 74246) * (327 / 125) + ((1) * (173535 / 148492) + ((0) * (-147294 / 115027) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 6: retain every product; norm_num then removes zero terms.
    change (-6 : ℝ) =
      ((7 / 30) * (-36) + ((4 / 3) * (5) + ((-221 / 100) * (-11554 / 325) + ((568463 / 74246) * (-21392 / 1875) + ((1) * (335549 / 74246) + ((0) * (-1983818 / 345081) + ((0) * (-1401 / 8183) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 7: retain every product; norm_num then removes zero terms.
    change (-8 : ℝ) =
      ((7 / 30) * (-36) + ((4 / 3) * (3) + ((-221 / 100) * (-9054 / 325) + ((568463 / 74246) * (-5464 / 625) + ((1) * (131327 / 74246) + ((0) * (-149846 / 345081) + ((0) * (1147 / 8183) + ((0) * (4186 / 37827) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 8: retain every product; norm_num then removes zero terms.
    change (-10 : ℝ) =
      ((7 / 30) * (-36) + ((4 / 3) * (-3) + ((-221 / 100) * (-1554 / 325) + ((568463 / 74246) * (-464 / 625) + ((1) * (-184355 / 74246) + ((0) * (479654 / 345081) + ((0) * (369 / 1169) + ((0) * (1648 / 12609) + ((0) * (136 / 2093) + 0)))))))))
    norm_num

#print axioms jacobian_lu_row_4
#assert_trust kernel jacobian_lu_row_4

end
end NLA.SP15
