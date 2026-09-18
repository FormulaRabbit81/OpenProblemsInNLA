/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

The homotopy starts at a nonzero scalar multiple of X^n, and never has
unit-circle roots. Degree drops at any other point remain allowed.
-/
import NLA.MF18.DiskHomotopy
import NLA.MF18.BoundaryNonvanishing

set_option autoImplicit false
open scoped BigOperators ComplexOrder

noncomputable section
namespace NLA.MF18

theorem scalarPencil_coeffContinuousOn {n : ℕ} (A B Q : ℝ → Mat n) (s : Set ℝ)
    (hA : ∀ i j, ContinuousOn (fun t => A t i j) s)
    (hB : ∀ i j, ContinuousOn (fun t => B t i j) s)
    (hQ : ∀ i j, ContinuousOn (fun t => Q t i j) s) :
    CoeffContinuousOn (fun t => scalarPencil (A t) (B t) (Q t)) s := by
  apply matrixDet_coeffContinuousOn
  intro i j
  exact coeffContinuousOn_add _ _
    (coeffContinuousOn_sub _ _
      (coeffContinuousOn_mul _ _ (coeffContinuousOn_C _ (hB i j))
        (coeffContinuousOn_const s (Polynomial.X ^ 2)))
      (coeffContinuousOn_mul _ _ (coeffContinuousOn_C _ (hQ i j))
        (coeffContinuousOn_const s Polynomial.X)))
    (coeffContinuousOn_C _ (hA i j))

theorem homotopy_coeffContinuousOn {n : ℕ} (C D R P : Mat n) (η : ℝ) (s : Set ℝ) :
    CoeffContinuousOn (homotopyPolynomial C D R P η) s := by
  apply scalarPencil_coeffContinuousOn
  · intro i j
    -- Evaluate the homotopy A matrix at (i,j); its complex scalar action is ordinary multiplication.
    change ContinuousOn (fun t : ℝ => (t : ℂ) * regularizedA C D η i j) s
    exact Complex.continuous_ofReal.continuousOn.mul continuousOn_const
  · intro i j
    -- Evaluate the homotopy B matrix at (i,j), retaining the explicit real-to-complex scalar cast.
    change ContinuousOn (fun t : ℝ => (t : ℂ) * regularizedB C D η i j) s
    exact Complex.continuous_ofReal.continuousOn.mul continuousOn_const
  · intro i j
    -- Evaluate the homotopy Q entry: t multiplies R, while the imaginary regularizer is constant.
    change ContinuousOn (fun t : ℝ => (t : ℂ) * R i j +
      (Complex.I * (η : ℂ)) * P i j) s
    exact (Complex.continuous_ofReal.continuousOn.mul continuousOn_const).add
      continuousOn_const

theorem homotopy_zero_polynomial {n : ℕ} (C D R P : Mat n) (η : ℝ) :
    homotopyPolynomial C D R P η 0 =
      Polynomial.C (((-(Complex.I * (η : ℂ))) • P).det) * Polynomial.X ^ n := by
  apply Polynomial.funext
  intro lam
  rw [homotopyPolynomial, pencil_evaluation]
  have heq : pencilValue ((0 : ℂ) • regularizedA C D η)
      ((0 : ℂ) • regularizedB C D η)
      ((0 : ℂ) • R + (Complex.I * (η : ℂ)) • P) lam =
        lam • ((-(Complex.I * (η : ℂ))) • P) := by
    ext i j
    simp only [pencilValue, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, zero_mul, mul_zero, zero_add, add_zero, zero_sub]
    ring
  simp only [Complex.ofReal_zero]
  rw [heq, Matrix.det_smul]
  simp only [Fintype.card_fin, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  exact mul_comm _ _

theorem homotopy_one_polynomial {n : ℕ} (C D R P : Mat n) (η : ℝ) :
    homotopyPolynomial C D R P η 1 = regularizedPolynomial C D R P η := by
  simp only [homotopyPolynomial, regularizedPolynomial, regularizedQ,
    Complex.ofReal_one, one_smul]

theorem homotopy_zero_disk_count {n : ℕ} (C D R P : Mat n)
    (hpos : CirclePositive P D) (η : ℝ) (hη : 0 < η) :
    diskRootCount (homotopyPolynomial C D R P η 0) = n := by
  classical
  have hp := (positive_average_and_sign P D hpos).1
  have hPdet : P.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det P).mp hp.isUnit |>.ne_zero
  have hηC : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hη)
  have hdet : ((-(Complex.I * (η : ℂ))) • P).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr
      (mul_ne_zero Complex.I_ne_zero hηC))) hPdet
  rw [homotopy_zero_polynomial]
  unfold diskRootCount
  rw [Polynomial.roots_C_mul_X_pow hdet, Multiset.nsmul_singleton]
  rw [Multiset.filter_eq_self.mpr ?_, Multiset.card_replicate]
  intro z hz
  have hz0 : z = 0 := Multiset.eq_of_mem_replicate hz
  simp only [hz0, norm_zero, zero_lt_one]

theorem regularized_root_count {n : ℕ} [NeZero n] (C D R P : Mat n)
    (hR : R.IsHermitian) (hP : P.IsHermitian) (hpos : CirclePositive P D)
    (η : ℝ) (hη : 0 < η) :
    diskRootCount (regularizedPolynomial C D R P η) = n ∧
    ∀ lam : ℂ, ‖lam‖ = 1 → (regularizedPolynomial C D R P η).eval lam ≠ 0 := by
  have heq := bounded_degree_disk_count_homotopy (2 * n)
    (homotopyPolynomial C D R P η)
    (homotopy_coeffContinuousOn C D R P η (Set.Icc 0 1))
    (fun t _ => pencil_degree_bound _ _ _)
    (fun t ht => homotopy_boundary_nonvanishing C D R P hR hP hpos η hη t ht)
  rw [homotopy_zero_disk_count C D R P hpos η hη, homotopy_one_polynomial] at heq
  refine ⟨heq.symm, ?_⟩
  simpa only [homotopy_one_polynomial] using
    homotopy_boundary_nonvanishing C D R P hR hP hpos η hη 1 (by simp)

#print axioms homotopy_coeffContinuousOn
#print axioms homotopy_zero_disk_count
#print axioms regularized_root_count

end NLA.MF18
