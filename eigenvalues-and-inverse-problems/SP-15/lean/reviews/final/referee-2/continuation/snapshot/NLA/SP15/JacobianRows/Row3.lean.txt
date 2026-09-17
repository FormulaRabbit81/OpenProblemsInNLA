/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

Row 3 of the frozen LU identity. Every typed change checks all nine actual
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

theorem jacobian_lu_row_3 (j : Fin 9) :
    jacobianMinor 3 j = (lowerCertificate * upperCertificate) 3 j := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases j
  · -- Column 0: retain every product; norm_num then removes zero terms.
    change (4 : ℝ) =
      ((1 / 75) * (300) + ((4 / 39) * (0) + ((-8 / 25) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 1: retain every product; norm_num then removes zero terms.
    change (4 : ℝ) =
      ((1 / 75) * (150) + ((4 / 39) * (39 / 2) + ((-8 / 25) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 2: retain every product; norm_num then removes zero terms.
    change (4 : ℝ) =
      ((1 / 75) * (100) + ((4 / 39) * (18) + ((-8 / 25) * (-100 / 39) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 3: retain every product; norm_num then removes zero terms.
    change (1 : ℝ) =
      ((1 / 75) * (84) + ((4 / 39) * (-1) + ((-8 / 25) * (20126 / 325) + ((1) * (37123 / 1875) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 4: retain every product; norm_num then removes zero terms.
    change (2 : ℝ) =
      ((1 / 75) * (90) + ((4 / 39) * (19 / 2) + ((-8 / 25) * (1447 / 65) + ((1) * (2606 / 375) + ((0) * (345081 / 148492) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 5: retain every product; norm_num then removes zero terms.
    change (3 : ℝ) =
      ((1 / 75) * (90) + ((4 / 39) * (27 / 2) + ((-8 / 25) * (447 / 65) + ((1) * (327 / 125) + ((0) * (173535 / 148492) + ((0) * (-147294 / 115027) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 6: retain every product; norm_num then removes zero terms.
    change (0 : ℝ) =
      ((1 / 75) * (-36) + ((4 / 39) * (5) + ((-8 / 25) * (-11554 / 325) + ((1) * (-21392 / 1875) + ((0) * (335549 / 74246) + ((0) * (-1983818 / 345081) + ((0) * (-1401 / 8183) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 7: retain every product; norm_num then removes zero terms.
    change (0 : ℝ) =
      ((1 / 75) * (-36) + ((4 / 39) * (3) + ((-8 / 25) * (-9054 / 325) + ((1) * (-5464 / 625) + ((0) * (131327 / 74246) + ((0) * (-149846 / 345081) + ((0) * (1147 / 8183) + ((0) * (4186 / 37827) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 8: retain every product; norm_num then removes zero terms.
    change (0 : ℝ) =
      ((1 / 75) * (-36) + ((4 / 39) * (-3) + ((-8 / 25) * (-1554 / 325) + ((1) * (-464 / 625) + ((0) * (-184355 / 74246) + ((0) * (479654 / 345081) + ((0) * (369 / 1169) + ((0) * (1648 / 12609) + ((0) * (136 / 2093) + 0)))))))))
    norm_num

#print axioms jacobian_lu_row_3
#assert_trust kernel jacobian_lu_row_3

end
end NLA.SP15
