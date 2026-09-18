/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

Weak stability of the limiting complementary matrix excludes every strictly
interior zero of its determinant polynomial. The value at zero is treated
separately, so no nonsingularity of B is required.
-/
import NLA.MF18.SolutionPolynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section
namespace NLA.MF18

theorem weak_complementary_disk_nonvanishing {n : ℕ} (B X : Mat n)
    (hweak : WeakStable (B * X⁻¹)) (z : ℂ) (hz : ‖z‖ < 1) :
    (complementaryPolynomial B X).eval z ≠ 0 := by
  by_cases hz0 : z = 0
  · subst z
    rw [complementary_evaluation]
    simp only [zero_smul, zero_sub, Matrix.det_neg, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  intro he
  have heq : z • (B * X⁻¹) - 1 =
      (-z) • (z⁻¹ • (1 : Mat n) - B * X⁻¹) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp [hz0] <;> ring
  rw [complementary_evaluation, heq, Matrix.det_smul, ← eval_charpoly_smul] at he
  have hroot : (B * X⁻¹).charpoly.IsRoot z⁻¹ :=
    (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr hz0))
  have hbound := hweak z⁻¹ hroot
  rw [norm_inv] at hbound
  exact (not_le_of_gt ((one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr hz)) hbound

theorem weak_complementary_disk_count {n : ℕ} (B X : Mat n)
    (hweak : WeakStable (B * X⁻¹)) : diskRootCount (complementaryPolynomial B X) = 0 := by
  classical
  unfold diskRootCount
  have he : (complementaryPolynomial B X).roots.filter (fun z => ‖z‖ < 1) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro z hz hzlt
    exact weak_complementary_disk_nonvanishing B X hweak z hzlt
      (Polynomial.isRoot_of_mem_roots hz)
  rw [he, Multiset.card_zero]

#print axioms weak_complementary_disk_count

end NLA.MF18
