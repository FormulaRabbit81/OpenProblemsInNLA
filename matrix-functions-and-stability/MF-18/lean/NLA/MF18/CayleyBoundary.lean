/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
-/
import NLA.MF18.CayleyAlgebra
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section
namespace NLA.MF18

theorem axis_cayley_denominator_ne_zero (z : ℂ) (hz : z.re = 0) : z + 1 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simpa [hz] using hre

theorem axis_cayley_norm (z : ℂ) (hz : z.re = 0) : ‖(z - 1) / (z + 1)‖ = 1 := by
  have hsq : ‖z - 1‖ ^ 2 = ‖z + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_sub, Complex.normSq_add, hz]
  have heq : ‖z - 1‖ = ‖z + 1‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  rw [norm_div, heq, div_self (norm_ne_zero_iff.mpr (axis_cayley_denominator_ne_zero z hz))]

theorem inverse_cayley_re_pos_iff (lam : ℂ) (hlam : lam ≠ 1) :
    0 < ((1 + lam) / (1 - lam)).re ↔ ‖lam‖ < 1 := by
  have hden : 0 < Complex.normSq (1 - lam) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hlam))
  have hre : ((1 + lam) / (1 - lam)).re =
      (1 - Complex.normSq lam) / Complex.normSq (1 - lam) := by
    rw [Complex.div_re]
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.add_im,
      Complex.sub_im, Complex.one_im, Complex.normSq_apply]
    ring
  rw [hre, div_pos_iff_of_pos_right hden, sub_pos, Complex.normSq_eq_norm_sq]
  simpa only [one_pow] using (sq_lt_sq₀ (norm_nonneg lam) (by norm_num : (0 : ℝ) ≤ 1))

theorem cayley_boundary_transfer (N : ℕ) (p : CPoly)
    (hd : p.natDegree ≤ N) (hb : ∀ lam : ℂ, ‖lam‖ = 1 → p.eval lam ≠ 0) :
    ∀ z : ℂ, z.re = 0 → (monicCayleyPolynomial N p).eval z ≠ 0 := by
  intro z hz
  have h1 : p.eval 1 ≠ 0 := hb 1 (by simp)
  unfold monicCayleyPolynomial
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    cayley_eval N p hd z (axis_cayley_denominator_ne_zero z hz)]
  exact mul_ne_zero (inv_ne_zero h1)
    (mul_ne_zero (pow_ne_zero _ (axis_cayley_denominator_ne_zero z hz))
      (hb _ (axis_cayley_norm z hz)))

#print axioms axis_cayley_norm
#print axioms inverse_cayley_re_pos_iff
#print axioms cayley_boundary_transfer

end NLA.MF18
