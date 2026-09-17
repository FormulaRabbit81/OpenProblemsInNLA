/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

Row 1 of the frozen LU identity. Every typed change checks all nine actual
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

theorem jacobian_lu_row_1 (j : Fin 9) :
    jacobianMinor 1 j = (lowerCertificate * upperCertificate) 1 j := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases j
  · -- Column 0: retain every product; norm_num then removes zero terms.
    change (75 : ℝ) =
      ((1 / 4) * (300) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 1: retain every product; norm_num then removes zero terms.
    change (57 : ℝ) =
      ((1 / 4) * (150) + ((1) * (39 / 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 2: retain every product; norm_num then removes zero terms.
    change (43 : ℝ) =
      ((1 / 4) * (100) + ((1) * (18) + ((0) * (-100 / 39) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 3: retain every product; norm_num then removes zero terms.
    change (20 : ℝ) =
      ((1 / 4) * (84) + ((1) * (-1) + ((0) * (20126 / 325) + ((0) * (37123 / 1875) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 4: retain every product; norm_num then removes zero terms.
    change (32 : ℝ) =
      ((1 / 4) * (90) + ((1) * (19 / 2) + ((0) * (1447 / 65) + ((0) * (2606 / 375) + ((0) * (345081 / 148492) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 5: retain every product; norm_num then removes zero terms.
    change (36 : ℝ) =
      ((1 / 4) * (90) + ((1) * (27 / 2) + ((0) * (447 / 65) + ((0) * (327 / 125) + ((0) * (173535 / 148492) + ((0) * (-147294 / 115027) + ((0) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 6: retain every product; norm_num then removes zero terms.
    change (-4 : ℝ) =
      ((1 / 4) * (-36) + ((1) * (5) + ((0) * (-11554 / 325) + ((0) * (-21392 / 1875) + ((0) * (335549 / 74246) + ((0) * (-1983818 / 345081) + ((0) * (-1401 / 8183) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 7: retain every product; norm_num then removes zero terms.
    change (-6 : ℝ) =
      ((1 / 4) * (-36) + ((1) * (3) + ((0) * (-9054 / 325) + ((0) * (-5464 / 625) + ((0) * (131327 / 74246) + ((0) * (-149846 / 345081) + ((0) * (1147 / 8183) + ((0) * (4186 / 37827) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 8: retain every product; norm_num then removes zero terms.
    change (-12 : ℝ) =
      ((1 / 4) * (-36) + ((1) * (-3) + ((0) * (-1554 / 325) + ((0) * (-464 / 625) + ((0) * (-184355 / 74246) + ((0) * (479654 / 345081) + ((0) * (369 / 1169) + ((0) * (1648 / 12609) + ((0) * (136 / 2093) + 0)))))))))
    norm_num

#print axioms jacobian_lu_row_1
#assert_trust kernel jacobian_lu_row_1

end
end NLA.SP15
