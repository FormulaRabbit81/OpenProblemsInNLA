/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. The full complex Green-function argument
is George Stepaniants's solution of the Guo--Kuo--Lin question.

The determinant degree estimate adapts the permutation-sum proof in
Mathlib.LinearAlgebra.Matrix.Polynomial (Yakov Pechersky) from entry degree one
to entry degree two. It does not assume an invertible leading coefficient.
-/
import NLA.MF18.Definitions
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Tactic.Abel

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF18

theorem pencil_evaluation {n : ℕ} (A B Q : Mat n) (lam : ℂ) :
    (scalarPencil A B Q).eval lam = (pencilValue A B Q lam).det := by
  unfold scalarPencil
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  -- At entry (i,j), the mapped evaluation ring hom is ordinary polynomial evaluation.
  change (matrixPolynomial A B Q i j).eval lam = (pencilValue A B Q lam) i j
  simp only [matrixPolynomial, pencilValue, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

private lemma entry_natDegree_le {n : ℕ} (A B Q : Mat n) (i j : Fin n) :
    (matrixPolynomial A B Q i j).natDegree ≤ 2 := by
  unfold matrixPolynomial
  compute_degree

theorem pencil_degree_bound {n : ℕ} (A B Q : Mat n) :
    (scalarPencil A B Q).natDegree ≤ 2 * n := by
  classical
  unfold scalarPencil
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  calc
    (Equiv.Perm.sign σ • ∏ i : Fin n, matrixPolynomial A B Q (σ i) i).natDegree ≤
        (∏ i : Fin n, matrixPolynomial A B Q (σ i) i).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]
      · rw [hs, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i : Fin n, (matrixPolynomial A B Q (σ i) i).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin n, 2 :=
      Finset.sum_le_sum fun i _ => entry_natDegree_le A B Q (σ i) i
    _ = 2 * n := by simp [Nat.mul_comm]

/-- Algebraic pencil factorization shared by the regularized and limiting equations. -/
theorem pencil_factorization {n : ℕ} (A B Q X : Mat n)
    (hX : X.det ≠ 0) (heq : X + B * X⁻¹ * A = Q) (lam : ℂ) :
    pencilValue A B Q lam =
      (lam • (B * X⁻¹) - 1) * X * (lam • (1 : Mat n) - X⁻¹ * A) := by
  have hu : IsUnit X.det := isUnit_iff_ne_zero.mpr hX
  have hleft : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hu
  have hright : X * (X⁻¹ * A) = A := Matrix.mul_nonsing_inv_cancel_left X A hu
  unfold pencilValue
  rw [← heq]
  simp only [smul_add, smul_sub, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_smul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul, hleft, hright,
    pow_two]
  abel

theorem solution_factorization {n : ℕ} (C D R P : Mat n) (η : ℝ) (X : Mat n)
    (h : IsStabilizingSolution C D R P η X) (lam : ℂ) :
    pencilValue (regularizedA C D η) (regularizedB C D η) (regularizedQ R P η) lam =
      (lam • (regularizedB C D η * X⁻¹) - 1) * X *
        (lam • (1 : Mat n) - X⁻¹ * regularizedA C D η) := by
  exact pencil_factorization (regularizedA C D η) (regularizedB C D η)
    (regularizedQ R P η) X h.1 h.2.1 lam

#print axioms pencil_evaluation
#print axioms pencil_degree_bound
#print axioms pencil_factorization
#print axioms solution_factorization

end NLA.MF18
