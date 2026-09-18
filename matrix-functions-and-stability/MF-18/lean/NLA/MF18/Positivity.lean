/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Source: George Stepaniants's complete
complex Green-function rank argument for the Guo--Kuo--Lin problem, Section 1.
-/
import NLA.MF18.Numerical
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped ComplexOrder

noncomputable section
namespace NLA.MF18

theorem positive_average_and_sign {n : ℕ} (P D : Mat n) (h : CirclePositive P D) :
    P.PosDef ∧ ∀ lam : ℂ, ‖lam‖ = 1 →
      (P - lam • D.conjTranspose - lam⁻¹ • D).PosDef := by
  have hplus : (P + D.conjTranspose + D).PosDef := by
    simpa using h (1 : ℂ) (by simp)
  have hminus : (P + -D.conjTranspose + -D).PosDef := by
    simpa using h (-1 : ℂ) (by simp)
  have havg : (1 / 2 : ℝ) •
      ((P + D.conjTranspose + D) + (P + -D.conjTranspose + -D)) = P := by
    ext i j
    norm_num [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, Complex.real_smul] <;>
      ring
  constructor
  · rw [← havg]
    exact (hplus.add hminus).smul certified_half.1
  · intro lam hlam
    simpa only [inv_neg, neg_smul, sub_eq_add_neg] using
      h (-lam) (by simpa only [norm_neg] using hlam)

#print axioms positive_average_and_sign
#assert_trust kernel positive_average_and_sign

end NLA.MF18
