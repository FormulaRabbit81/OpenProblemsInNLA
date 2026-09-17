/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

Row 8 of the frozen LU identity. Every typed change checks all nine actual
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

theorem jacobian_lu_row_8 (j : Fin 9) :
    jacobianMinor 8 j = (lowerCertificate * upperCertificate) 8 j := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases j
  · -- Column 0: retain every product; norm_num then removes zero terms.
    change (40 : ℝ) =
      ((2 / 15) * (300) + ((28 / 39) * (0) + ((-107 / 100) * (0) + ((359171 / 74246) * (0) + ((799091 / 345081) * (0) + ((79979 / 147294) * (0) + ((216673 / 37827) * (0) + ((8825 / 2093) * (0) + ((1) * (0) + 0)))))))))
    norm_num
  · -- Column 1: retain every product; norm_num then removes zero terms.
    change (34 : ℝ) =
      ((2 / 15) * (150) + ((28 / 39) * (39 / 2) + ((-107 / 100) * (0) + ((359171 / 74246) * (0) + ((799091 / 345081) * (0) + ((79979 / 147294) * (0) + ((216673 / 37827) * (0) + ((8825 / 2093) * (0) + ((1) * (0) + 0)))))))))
    norm_num
  · -- Column 2: retain every product; norm_num then removes zero terms.
    change (29 : ℝ) =
      ((2 / 15) * (100) + ((28 / 39) * (18) + ((-107 / 100) * (-100 / 39) + ((359171 / 74246) * (0) + ((799091 / 345081) * (0) + ((79979 / 147294) * (0) + ((216673 / 37827) * (0) + ((8825 / 2093) * (0) + ((1) * (0) + 0)))))))))
    norm_num
  · -- Column 3: retain every product; norm_num then removes zero terms.
    change (40 : ℝ) =
      ((2 / 15) * (84) + ((28 / 39) * (-1) + ((-107 / 100) * (20126 / 325) + ((359171 / 74246) * (37123 / 1875) + ((799091 / 345081) * (0) + ((79979 / 147294) * (0) + ((216673 / 37827) * (0) + ((8825 / 2093) * (0) + ((1) * (0) + 0)))))))))
    norm_num
  · -- Column 4: retain every product; norm_num then removes zero terms.
    change (34 : ℝ) =
      ((2 / 15) * (90) + ((28 / 39) * (19 / 2) + ((-107 / 100) * (1447 / 65) + ((359171 / 74246) * (2606 / 375) + ((799091 / 345081) * (345081 / 148492) + ((79979 / 147294) * (0) + ((216673 / 37827) * (0) + ((8825 / 2093) * (0) + ((1) * (0) + 0)))))))))
    norm_num
  · -- Column 5: retain every product; norm_num then removes zero terms.
    change (29 : ℝ) =
      ((2 / 15) * (90) + ((28 / 39) * (27 / 2) + ((-107 / 100) * (447 / 65) + ((359171 / 74246) * (327 / 125) + ((799091 / 345081) * (173535 / 148492) + ((79979 / 147294) * (-147294 / 115027) + ((216673 / 37827) * (0) + ((8825 / 2093) * (0) + ((1) * (0) + 0)))))))))
    norm_num
  · -- Column 6: retain every product; norm_num then removes zero terms.
    change (-12 : ℝ) =
      ((2 / 15) * (-36) + ((28 / 39) * (5) + ((-107 / 100) * (-11554 / 325) + ((359171 / 74246) * (-21392 / 1875) + ((799091 / 345081) * (335549 / 74246) + ((79979 / 147294) * (-1983818 / 345081) + ((216673 / 37827) * (-1401 / 8183) + ((8825 / 2093) * (0) + ((1) * (0) + 0)))))))))
    norm_num
  · -- Column 7: retain every product; norm_num then removes zero terms.
    change (-10 : ℝ) =
      ((2 / 15) * (-36) + ((28 / 39) * (3) + ((-107 / 100) * (-9054 / 325) + ((359171 / 74246) * (-5464 / 625) + ((799091 / 345081) * (131327 / 74246) + ((79979 / 147294) * (-149846 / 345081) + ((216673 / 37827) * (1147 / 8183) + ((8825 / 2093) * (4186 / 37827) + ((1) * (0) + 0)))))))))
    norm_num
  · -- Column 8: retain every product; norm_num then removes zero terms.
    change (-8 : ℝ) =
      ((2 / 15) * (-36) + ((28 / 39) * (-3) + ((-107 / 100) * (-1554 / 325) + ((359171 / 74246) * (-464 / 625) + ((799091 / 345081) * (-184355 / 74246) + ((79979 / 147294) * (479654 / 345081) + ((216673 / 37827) * (369 / 1169) + ((8825 / 2093) * (1648 / 12609) + ((1) * (136 / 2093) + 0)))))))))
    norm_num

#print axioms jacobian_lu_row_8
#assert_trust kernel jacobian_lu_row_8

end
end NLA.SP15
