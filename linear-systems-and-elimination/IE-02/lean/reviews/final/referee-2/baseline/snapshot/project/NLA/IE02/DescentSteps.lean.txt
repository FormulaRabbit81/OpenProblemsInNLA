/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance; prior mathematical attribution retained.

All parameter-dependent bounds are symbolic. The kernel certificate for the
positive half is genuinely consumed when proving positivity of each step.
-/
import NLA.IE02.Numerical

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

private theorem half_min_bounds (a : ℝ) (ha : 0 < a) :
    0 < (1 / 2 : ℝ) * min 1 a ∧
    (1 / 2 : ℝ) * min 1 a ≤ 1 ∧ (1 / 2 : ℝ) * min 1 a ≤ a := by
  have hm : 0 < min 1 a := lt_min (by norm_num) ha
  have hpos := mul_pos half_certificate hm
  have hle : (1 / 2 : ℝ) * min 1 a ≤ min 1 a := by linarith
  exact ⟨hpos, hle.trans (min_le_left 1 a), hle.trans (min_le_right 1 a)⟩

theorem descent_step_bounds {n : ℕ} (T D : Square n) (γ β : ℝ)
    (hγ : 0 < γ) (hβ : 0 < β) :
    0 < emptyStep D γ ∧ emptyStep D γ ≤ 1 ∧
    emptyStep D γ ≤ γ / (2 * (descentL D + 1)) ∧
    0 < gapStep T D γ β ∧ gapStep T D γ β ≤ 1 ∧
    gapStep T D γ β ≤ γ / (2 * (descentL D + 1)) ∧
    gapStep T D γ β ≤ β / (2 * (descentC T D + 1)) := by
  have hL : 0 ≤ descentL D := sq_nonneg (operatorNorm D)
  have hC : 0 ≤ descentC T D := by
    dsimp only [descentC, descentL, operatorNorm]
    positivity
  have ha : 0 < γ / (2 * (descentL D + 1)) := div_pos hγ (by positivity)
  have hb : 0 < β / (2 * (descentC T D + 1)) := div_pos hβ (by positivity)
  have he := half_min_bounds _ ha
  have hg := half_min_bounds _ (lt_min ha hb)
  exact ⟨he.1, he.2.1, he.2.2, hg.1, hg.2.1,
    hg.2.2.trans (min_le_left _ _), hg.2.2.trans (min_le_right _ _)⟩

#print axioms descent_step_bounds
#assert_trust kernel descent_step_bounds

end
end NLA.IE02
