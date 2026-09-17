/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original attribution is retained in
Definitions.lean and SourceCorrespondence.md. Mathlib supplies Cauchy-Schwarz
and real ordered-field arithmetic. The half certificate is consumed through
DescentSteps. No interval subdivision or eigenvalue computation is needed.

The frozen hne and the conditional gap theorem's hK can be redundant for the
stronger pointwise implications; they are retained without artificial uses.
-/
import NLA.IE02.NormAttainment
import NLA.IE02.DescentSteps
import NLA.IE02.DescentQuadratic
import NLA.IE02.DescentGap

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

private theorem unit_action_le {n : ℕ} (A : Square n) (x : H n) (hx : ‖x‖ = 1) :
    ‖euclideanLin A x‖ ≤ operatorNorm A := by
  have h : ‖euclideanLin A x‖ ≤ operatorNorm A * ‖x‖ :=
    (euclideanCLM A).le_opNorm x
  simpa only [hx, mul_one] using h

private theorem unit_action_sq_le {n : ℕ} (A : Square n) (x : H n) (hx : ‖x‖ = 1) :
    ‖euclideanLin A x‖ ^ 2 ≤ operatorNorm A ^ 2 :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg (euclideanCLM A))).mpr (unit_action_le A x hx)

private theorem unit_form_lower {n : ℕ} (T D : Square n) (x : H n) (hx : ‖x‖ = 1) :
    -(operatorNorm T * operatorNorm D) ≤ descentForm T D x := by
  have hinner : ‖inner ℂ (euclideanLin T x) (euclideanLin D x)‖ ≤
      operatorNorm T * operatorNorm D :=
    (norm_inner_le_norm _ _).trans
      (mul_le_mul (unit_action_le T x hx) (unit_action_le D x hx)
        (norm_nonneg _) (norm_nonneg (euclideanCLM T)))
  have hreal := (abs_le.mp (Complex.abs_re_le_norm
    (inner ℂ (euclideanLin T x) (euclideanLin D x)))).1
  -- Expose the frozen descentForm as a real part so the real inequalities apply.
  change -(operatorNorm T * operatorNorm D) ≤
    (inner ℂ (euclideanLin T x) (euclideanLin D x)).re
  linarith

private theorem high_form_decrease {n : ℕ} (T D : Square n) (x : H n)
    (hx : ‖x‖ = 1) (ε γ : ℝ) (hε : 0 < ε)
    (hstep : ε ≤ γ / (2 * (descentL D + 1)))
    (hform : γ / 2 < descentForm T D x) :
    ‖euclideanLin (T - (ε : ℂ) • D) x‖ ^ 2 < operatorNorm T ^ 2 := by
  have hL : 0 ≤ descentL D := sq_nonneg (operatorNorm D)
  have hden : 0 < 2 * (descentL D + 1) := by positivity
  have hcleared := (le_div_iff₀ hden).mp hstep
  have hcoeff : ε * descentL D < γ := by
    nlinarith [mul_nonneg hε.le hL]
  have hD : ‖euclideanLin D x‖ ^ 2 ≤ descentL D := unit_action_sq_le D x hx
  have hquad : ε ^ 2 * ‖euclideanLin D x‖ ^ 2 < ε * γ := by
    calc
      ε ^ 2 * ‖euclideanLin D x‖ ^ 2 ≤ ε ^ 2 * descentL D :=
        mul_le_mul_of_nonneg_left hD (sq_nonneg ε)
      _ = ε * (ε * descentL D) := by ring
      _ < ε * γ := mul_lt_mul_of_pos_left hcoeff hε
  have hlinear : ε * γ < 2 * ε * descentForm T D x := by
    nlinarith [mul_pos hε (sub_pos.mpr hform)]
  have hT := unit_action_sq_le T x hx
  rw [descent_quadratic_expansion]
  nlinarith only [hquad, hlinear, hT]

private theorem low_form_decrease {n : ℕ} (T D : Square n) (x : H n)
    (hx : ‖x‖ = 1) (ε β : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hstep : ε ≤ β / (2 * (descentC T D + 1)))
    (hgap : ‖euclideanLin T x‖ ^ 2 ≤ operatorNorm T ^ 2 - β) :
    ‖euclideanLin (T - (ε : ℂ) • D) x‖ ^ 2 < operatorNorm T ^ 2 := by
  have hL : 0 ≤ descentL D := sq_nonneg (operatorNorm D)
  have hC : 0 ≤ descentC T D := by
    unfold descentC descentL operatorNorm
    positivity
  have hden : 0 < 2 * (descentC T D + 1) := by positivity
  have hcleared := (le_div_iff₀ hden).mp hstep
  have hcoeff : ε * descentC T D < β := by
    nlinarith [mul_nonneg hε.le hC]
  have hD : ‖euclideanLin D x‖ ^ 2 ≤ descentL D := unit_action_sq_le D x hx
  have hpow : ε ^ 2 ≤ ε := by nlinarith
  have hquad : ε ^ 2 * ‖euclideanLin D x‖ ^ 2 ≤ ε * descentL D :=
    (mul_le_mul_of_nonneg_left hD (sq_nonneg ε)).trans
      (mul_le_mul_of_nonneg_right hpow hL)
  have hf := unit_form_lower T D x hx
  -- Multiplying by the nonnegative real 2 * ε preserves the lower bound's order.
  have hlinear := mul_le_mul_of_nonneg_left hf (show 0 ≤ 2 * ε by positivity)
  rw [descent_quadratic_expansion]
  dsimp only [descentC] at hcoeff
  nlinarith only [hgap, hquad, hlinear, hcoeff]

theorem descent_empty_complement {n : ℕ} (hn : 1 ≤ n) (T D : Square n)
    (hne : T ≠ 0) (γ : ℝ) (hγ : 0 < γ) (hK : descentComplement T D γ = ∅) :
    operatorNorm (T - (emptyStep D γ : ℂ) • D) < operatorNorm T := by
  have hs := descent_step_bounds T D γ 1 hγ (by norm_num)
  obtain ⟨x, hx, hat⟩ := (euclidean_norm_attainment hn
    (T - (emptyStep D γ : ℂ) • D)).2.2.2
  have hform : γ / 2 < descentForm T D x := by
    apply lt_of_not_ge
    intro hle
    have hxK : x ∈ descentComplement T D γ := ⟨hx, hle⟩
    rw [hK] at hxK
    exact hxK
  apply (sq_lt_sq₀ (norm_nonneg (euclideanCLM _))
    (norm_nonneg (euclideanCLM T))).mp
  -- Restore the frozen operatorNorm wrapper after the squared-norm equivalence.
  change operatorNorm (T - (emptyStep D γ : ℂ) • D) ^ 2 < operatorNorm T ^ 2
  rw [← hat]
  exact high_form_decrease T D x hx _ γ hs.1 hs.2.2.1 hform

theorem descent_nonempty_complement {n : ℕ} (hn : 1 ≤ n) (T D : Square n)
    (hne : T ≠ 0) (γ β : ℝ) (hγ : 0 < γ) (hβ : 0 < β)
    (hK : (descentComplement T D γ).Nonempty)
    (hgap : ∀ x ∈ descentComplement T D γ,
      ‖euclideanLin T x‖ ^ 2 ≤ operatorNorm T ^ 2 - β) :
    operatorNorm (T - (gapStep T D γ β : ℂ) • D) < operatorNorm T := by
  have hs := (descent_step_bounds T D γ β hγ hβ).2.2.2
  obtain ⟨x, hx, hat⟩ := (euclidean_norm_attainment hn
    (T - (gapStep T D γ β : ℂ) • D)).2.2.2
  apply (sq_lt_sq₀ (norm_nonneg (euclideanCLM _))
    (norm_nonneg (euclideanCLM T))).mp
  -- Restore the frozen operatorNorm wrapper after the squared-norm equivalence.
  change operatorNorm (T - (gapStep T D γ β : ℂ) • D) ^ 2 < operatorNorm T ^ 2
  rw [← hat]
  by_cases hc : x ∈ descentComplement T D γ
  · exact low_form_decrease T D x hx _ β hs.1 hs.2.1 hs.2.2.2 (hgap x hc)
  · have hform : γ / 2 < descentForm T D x := by
      apply lt_of_not_ge
      intro hle
      exact hc ⟨hx, hle⟩
    exact high_form_decrease T D x hx _ γ hs.1 hs.2.2.1 hform

theorem positive_gradient_descent {n : ℕ} (hn : 1 ≤ n) (T D : Square n)
    (hne : T ≠ 0) (γ : ℝ) (hγ : 0 < γ)
    (hpos : ∀ x ∈ unitMaximal T, γ ≤ descentForm T D x) :
    ∃ ε : ℝ, 0 < ε ∧ operatorNorm (T - (ε : ℂ) • D) < operatorNorm T := by
  by_cases hK : (descentComplement T D γ).Nonempty
  · obtain ⟨β, hβ, hgap⟩ := descent_complement_gap hn T D hne γ hγ hpos hK
    exact ⟨gapStep T D γ β, (descent_step_bounds T D γ β hγ hβ).2.2.2.1,
      descent_nonempty_complement hn T D hne γ β hγ hβ hK hgap⟩
  · exact ⟨emptyStep D γ, (descent_step_bounds T D γ 1 hγ (by norm_num)).1,
      descent_empty_complement hn T D hne γ hγ (Set.not_nonempty_iff_eq_empty.mp hK)⟩

#print axioms descent_empty_complement
#assert_trust kernel descent_empty_complement
#print axioms descent_nonempty_complement
#assert_trust kernel descent_nonempty_complement
#print axioms positive_gradient_descent
#assert_trust kernel positive_gradient_descent

end
end NLA.IE02
