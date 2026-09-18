/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
-/
import NLA.MF18.RegularizedCount
import NLA.MF18.SolutionPolynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

noncomputable section
namespace NLA.MF18

theorem complementary_closed_disk_nonvanishing {n : ℕ} [NeZero n]
    (C D R P : Mat n) (hR : R.IsHermitian) (hP : P.IsHermitian)
    (hpos : CirclePositive P D) (η : ℝ) (hη : 0 < η) (X : Mat n)
    (hX : IsStabilizingSolution C D R P η X) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → (complementaryPolynomial (regularizedB C D η) X).eval z ≠ 0 := by
  have hreg := regularized_root_count C D R P hR hP hpos η hη
  have hfactor := solution_polynomial_factorization C D R P η X hX
  have hq := complementary_ne_zero (regularizedB C D η) X
  have hprod : complementaryPolynomial (regularizedB C D η) X *
      (X⁻¹ * regularizedA C D η).charpoly ≠ 0 :=
    mul_ne_zero hq (Matrix.charpoly_monic _).ne_zero
  have hsum := hreg.1
  rw [hfactor, diskRootCount_C_mul X.det hX.1,
    diskRootCount_mul _ _ hprod, strictStable_disk_count _ hX.2.2] at hsum
  have hzero : diskRootCount (complementaryPolynomial (regularizedB C D η) X) = 0 := by
    omega
  intro z hz
  rcases lt_or_eq_of_le hz with hzlt | hzeq
  · exact diskRootCount_zero_no_root _ hq hzero z hzlt
  · intro he
    apply hreg.2 z hzeq
    rw [hfactor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul, he,
      zero_mul, mul_zero]

theorem complementary_stability {n : ℕ} [NeZero n] (C D R P : Mat n)
    (hR : R.IsHermitian) (hP : P.IsHermitian) (hpos : CirclePositive P D)
    (η : ℝ) (hη : 0 < η) (X : Mat n)
    (hX : IsStabilizingSolution C D R P η X) :
    StrictStable (regularizedB C D η * X⁻¹) := by
  intro μ hroot
  by_contra hnot
  have hge : 1 ≤ ‖μ‖ := le_of_not_gt hnot
  have hμ0 : μ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le hge))
  have hinv : ‖μ⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (zero_lt_one.trans_le hge)).mpr hge
  have he : (complementaryPolynomial (regularizedB C D η) X).eval μ⁻¹ = 0 := by
    rw [complementary_evaluation]
    have heq : μ⁻¹ • (regularizedB C D η * X⁻¹) - 1 =
        (-μ⁻¹) • (μ • (1 : Mat n) - regularizedB C D η * X⁻¹) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      field_simp [hμ0] <;> ring
    rw [heq, Matrix.det_smul, ← eval_charpoly_smul, hroot, mul_zero]
  exact (complementary_closed_disk_nonvanishing C D R P hR hP hpos η hη X hX μ⁻¹ hinv) he

#print axioms complementary_stability

end NLA.MF18
