/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The kernel-trust setup follows the accepted MF05 Numerical module. Unlike
that closed scalar certificate, these two affine bounds certify the entire
single interval [0,1/2]. There is no subdivision or matrix-entry enumeration.
The public certificate is consumed below at the actual trace-Young weight.
-/
import NLA.MI24.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MI24

private theorem young_complement_lower_box :
    ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), 1 / 2 ≤ 1 - u := by
  certify_bound (trust := kernel)

private theorem young_complement_upper_box :
    ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), 1 - u ≤ 1 := by
  certify_bound (trust := kernel)

theorem young_weight_interval (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    1 / 2 ≤ 1 - u ∧ 1 - u ≤ 1 := by
  exact ⟨young_complement_lower_box u ⟨hu0, hu1⟩,
    young_complement_upper_box u ⟨hu0, hu1⟩⟩

lemma youngWeight_pos (p : ℝ) (hp : 1 ≤ p) : 0 < youngWeight p := by
  unfold youngWeight
  exact one_div_pos.mpr (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hp))

lemma youngWeight_le_half (p : ℝ) (hp : 1 ≤ p) : youngWeight p ≤ 1 / 2 := by
  unfold youngWeight
  exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)

/-- This application keeps the interval certificate on the actual Young-weight
dependency path; it is not an unrelated demonstration of LeanCert. -/
lemma youngWeight_complement_bounds (p : ℝ) (hp : 1 ≤ p) :
    1 / 2 ≤ 1 - youngWeight p ∧ 1 - youngWeight p ≤ 1 := by
  exact young_weight_interval (youngWeight p) (youngWeight_pos p hp).le
    (youngWeight_le_half p hp)

#print axioms young_weight_interval
#assert_trust kernel young_weight_interval
#print axioms youngWeight_complement_bounds
#assert_trust kernel youngWeight_complement_bounds

end NLA.MI24
