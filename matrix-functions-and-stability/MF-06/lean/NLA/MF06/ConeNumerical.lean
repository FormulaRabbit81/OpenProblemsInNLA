/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

All cone parameters are arbitrary real numbers in their frozen ranges. The
inequalities are symbolic. Strict positivity of the retained growth factor
actually consumes MF05's source-pinned kernel-mode LeanCert half certificate.
-/
import NLA.MF06.Definitions
import NLA.MF05.Numerical

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF05

/-- C09: cone invariance and a certified positive retained growth factor. -/
theorem cone_numerical_bound (q K t : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hK : 0 ≤ K) (ht0 : 0 ≤ t) (ht : t ≤ 1 / coneLoss q K ^ 2) :
    1 ≤ coneHeight q K ∧ 2 ≤ coneLoss q K ∧
    q * coneHeight q K + K = coneHeight q K - 1 ∧
    coneHeight q K - 1 + coneLoss q K * t ≤
      coneHeight q K * (1 - coneLoss q K * t) ∧
    localRadius ≤ 1 - coneLoss q K * t ∧
    0 < 1 - coneLoss q K * t := by
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hH : 1 ≤ coneHeight q K := by
    apply (le_div_iff₀ hden).mpr
    linarith
  have hL : 2 ≤ coneLoss q K := by
    dsimp only [coneLoss]
    linarith
  have hLpos : 0 < coneLoss q K := lt_of_lt_of_le (by norm_num) hL
  have hidentity : q * coneHeight q K + K = coneHeight q K - 1 := by
    have hmul : coneHeight q K * (1 - q) = K + 1 :=
      div_mul_cancel₀ (K + 1) hden.ne'
    nlinarith
  have hquadratic : t * coneLoss q K ^ 2 ≤ 1 :=
    (le_div_iff₀ (pow_pos hLpos 2)).mp ht
  have hcone : coneHeight q K - 1 + coneLoss q K * t ≤
      coneHeight q K * (1 - coneLoss q K * t) := by
    dsimp only [coneLoss] at hquadratic ⊢
    nlinarith
  have hhalf : coneLoss q K * t ≤ (1 : ℝ) / 2 := by
    have hdouble := mul_le_mul_of_nonneg_right hL (mul_nonneg hLpos.le ht0)
    nlinarith
  have hfactor : localRadius ≤ 1 - coneLoss q K * t := by
    dsimp only [localRadius]
    linarith
  exact ⟨hH, hL, hidentity, hcone, hfactor, half_radius_certificate.1.trans_le hfactor⟩

#print axioms cone_numerical_bound
#assert_trust kernel cone_numerical_bound

end NLA.MF06
