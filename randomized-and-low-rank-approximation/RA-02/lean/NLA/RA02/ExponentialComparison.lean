/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.
-/
import NLA.RA02.ExpectationLower
import NLA.RA02.ArrowheadTail
import NLA.RA02.Numerical
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Archimedean

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

theorem binomial_exponential_bound (r : ℕ) (hr : 1 ≤ r) :
    (1 + 1 / (r : ℝ)) ^ r ≤ Real.exp 1 := by
  simpa only [one_div] using (Real.one_add_inv_pow_le_exp (n := r))

theorem exponential_tail_factor (r : ℕ) (hr : 1 ≤ r) (hA : (arrowhead r).IsHermitian) :
    ((2 : ℝ) ^ r / 3) * rankTail (arrowhead r) hA r ≤ expectedTrace (arrowhead r) r := by
  have htail := (arrowhead_tail r hr hA).2
  have hden : 0 < (1 + 1 / (r : ℝ)) ^ r := by positivity
  have hnum : 0 ≤ (2 : ℝ) ^ r * scaleParameter r ^ r := by
    exact mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (scaleParameter_pos r).le _)
  calc
    ((2 : ℝ) ^ r / 3) * rankTail (arrowhead r) hA r ≤
        ((2 : ℝ) ^ r / 3) * scaleParameter r ^ r :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = (2 : ℝ) ^ r * scaleParameter r ^ r / 3 := by ring
    _ ≤ (2 : ℝ) ^ r * scaleParameter r ^ r / (1 + 1 / (r : ℝ)) ^ r :=
      div_le_div_of_nonneg_left hnum hden (rank_denominator_le_three r)
    _ ≤ expectedTrace (arrowhead r) r := expectation_lower_bound r hr

theorem exponential_dominates_real_power (C p : ℝ) (hC : 0 < C) (hp : 0 ≤ p) :
    ∃ r : ℕ, 1 ≤ r ∧ 3 * C * Real.rpow (r : ℝ) p < (2 : ℝ) ^ r := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := (isLittleO_rpow_exp_pos_mul_atTop p hlog).def
    (show 0 < 1 / (6 * C) by positivity)
  obtain ⟨N, hN⟩ := hsmall.natCast_atTop.exists_forall_of_atTop
  let r : ℕ := max N 1
  have hr : 1 ≤ r := Nat.le_max_right _ _
  have hbound := hN r (Nat.le_max_left _ _)
  have hnonneg : 0 ≤ Real.rpow (r : ℝ) p := Real.rpow_nonneg (Nat.cast_nonneg r) p
  change ‖Real.rpow (r : ℝ) p‖ ≤
    (1 / (6 * C)) * ‖Real.exp (Real.log 2 * (r : ℝ))‖ at hbound
  simp only [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_pos (Real.exp_pos _)] at hbound
  have hexp : Real.exp (Real.log 2 * (r : ℝ)) = (2 : ℝ) ^ r := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hexp] at hbound
  have hscaled := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 6 * C by positivity)
  have hcancel : (6 * C) * ((1 / (6 * C)) * (2 : ℝ) ^ r) = (2 : ℝ) ^ r := by
    field_simp [hC.ne'] <;> ring
  rw [hcancel] at hscaled
  refine ⟨r, hr, ?_⟩
  have htwo : 0 < (2 : ℝ) ^ r := pow_pos (by norm_num) r
  nlinarith only [hscaled, htwo]

#print axioms binomial_exponential_bound
#assert_trust kernel binomial_exponential_bound
#print axioms exponential_tail_factor
#assert_trust kernel exponential_tail_factor
#print axioms exponential_dominates_real_power
#assert_trust kernel exponential_dominates_real_power

end
end NLA.RA02
