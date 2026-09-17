/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

Row 6 of the frozen LU identity. Every typed change checks all nine actual
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

theorem jacobian_lu_row_6 (j : Fin 9) :
    jacobianMinor 6 j = (lowerCertificate * upperCertificate) 6 j := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases j
  · -- Column 0: retain every product; norm_num then removes zero terms.
    change (1 : ℝ) =
      ((1 / 300) * (300) + ((1 / 39) * (0) + ((-2 / 25) * (0) + ((10687 / 37123) * (0) + ((3196 / 31371) * (0) + ((-407 / 16366) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 1: retain every product; norm_num then removes zero terms.
    change (1 : ℝ) =
      ((1 / 300) * (150) + ((1 / 39) * (39 / 2) + ((-2 / 25) * (0) + ((10687 / 37123) * (0) + ((3196 / 31371) * (0) + ((-407 / 16366) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 2: retain every product; norm_num then removes zero terms.
    change (1 : ℝ) =
      ((1 / 300) * (100) + ((1 / 39) * (18) + ((-2 / 25) * (-100 / 39) + ((10687 / 37123) * (0) + ((3196 / 31371) * (0) + ((-407 / 16366) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 3: retain every product; norm_num then removes zero terms.
    change (1 : ℝ) =
      ((1 / 300) * (84) + ((1 / 39) * (-1) + ((-2 / 25) * (20126 / 325) + ((10687 / 37123) * (37123 / 1875) + ((3196 / 31371) * (0) + ((-407 / 16366) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 4: retain every product; norm_num then removes zero terms.
    change (1 : ℝ) =
      ((1 / 300) * (90) + ((1 / 39) * (19 / 2) + ((-2 / 25) * (1447 / 65) + ((10687 / 37123) * (2606 / 375) + ((3196 / 31371) * (345081 / 148492) + ((-407 / 16366) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 5: retain every product; norm_num then removes zero terms.
    change (1 : ℝ) =
      ((1 / 300) * (90) + ((1 / 39) * (27 / 2) + ((-2 / 25) * (447 / 65) + ((10687 / 37123) * (327 / 125) + ((3196 / 31371) * (173535 / 148492) + ((-407 / 16366) * (-147294 / 115027) + ((1) * (0) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 6: retain every product; norm_num then removes zero terms.
    change (0 : ℝ) =
      ((1 / 300) * (-36) + ((1 / 39) * (5) + ((-2 / 25) * (-11554 / 325) + ((10687 / 37123) * (-21392 / 1875) + ((3196 / 31371) * (335549 / 74246) + ((-407 / 16366) * (-1983818 / 345081) + ((1) * (-1401 / 8183) + ((0) * (0) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 7: retain every product; norm_num then removes zero terms.
    change (0 : ℝ) =
      ((1 / 300) * (-36) + ((1 / 39) * (3) + ((-2 / 25) * (-9054 / 325) + ((10687 / 37123) * (-5464 / 625) + ((3196 / 31371) * (131327 / 74246) + ((-407 / 16366) * (-149846 / 345081) + ((1) * (1147 / 8183) + ((0) * (4186 / 37827) + ((0) * (0) + 0)))))))))
    norm_num
  · -- Column 8: retain every product; norm_num then removes zero terms.
    change (0 : ℝ) =
      ((1 / 300) * (-36) + ((1 / 39) * (-3) + ((-2 / 25) * (-1554 / 325) + ((10687 / 37123) * (-464 / 625) + ((3196 / 31371) * (-184355 / 74246) + ((-407 / 16366) * (479654 / 345081) + ((1) * (369 / 1169) + ((0) * (1648 / 12609) + ((0) * (136 / 2093) + 0)))))))))
    norm_num

#print axioms jacobian_lu_row_6
#assert_trust kernel jacobian_lu_row_6

end
end NLA.SP15
