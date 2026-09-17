/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

Small exact identities used by the shifted determinant proof. Matrix products
retain their order. The module tactic only normalizes scalar coefficients of
the fixed matrix atoms; it never assumes that two matrices commute.
-/
import NLA.SP15.SchurPositivity
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped Matrix

theorem scalar_matrix_inv (s : ℂ) (hs : s ≠ 0)
    [Invertible (s • (1 : Square 3))] :
    ⅟(s • (1 : Square 3)) = s⁻¹ • (1 : Square 3) := by
  apply invOf_eq_right_inv
  simp [smul_smul, hs]

theorem first_schur_root_product (s z : ℂ) (R : Square 3) :
    ((-z) • R.conjTranspose) * (s⁻¹ • (1 : Square 3)) * ((-star z) • R) =
      ((Complex.normSq z : ℂ) / s) • (R.conjTranspose * R) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  congr 1
  rw [div_eq_mul_inv, Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
  ring

theorem scalar_square_commutes (s c : ℂ) (S : Square 3) :
    (s • (1 : Square 3) + S * S) * (c • S) =
      (c • S) * (s • (1 : Square 3) + S * S) := by
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_smul, Matrix.mul_assoc]
  module

theorem determinant_lower_commuting (X B C D : Square 3) [Invertible D]
    (hCD : C * D = D * C) :
    (Matrix.fromBlocks X B C D).det = (X * D - B * C).det := by
  have hcancel : B * ⅟D * C * D = B * C := by
    calc
      B * ⅟D * C * D = B * (⅟D * (C * D)) := by simp only [Matrix.mul_assoc]
      _ = B * (⅟D * (D * C)) := by rw [hCD]
      _ = B * C := by rw [← Matrix.mul_assoc (⅟D) D C, invOf_mul_self, Matrix.one_mul]
  calc
    (Matrix.fromBlocks X B C D).det = D.det * (X - B * ⅟D * C).det :=
      Matrix.det_fromBlocks₂₂ X B C D
    _ = ((X - B * ⅟D * C) * D).det := by rw [Matrix.det_mul, mul_comm]
    _ = (X * D - B * C).det := by rw [sub_mul, hcancel]

theorem first_schur_diagonal (P : Square 3) (s t ρ : ℂ)
    (hs : s ≠ 0) (hst : s = t + ρ) :
    s • (1 : Square 3) + P - (ρ / s) • P =
      s • (1 : Square 3) + (t / s) • P := by
  have hc : 1 - ρ / s = t / s := by
    field_simp [hs]
    rw [hst]
    ring
  calc
    s • (1 : Square 3) + P - (ρ / s) • P =
        s • (1 : Square 3) + (1 - ρ / s) • P := by module
    _ = s • (1 : Square 3) + (t / s) • P := by rw [hc]

theorem final_schur_matrix (P Q : Square 3) (s t ρ : ℂ)
    (hs : s ≠ 0) (ht : t ≠ 0) (hst : s = t + ρ) :
    (s • (1 : Square 3) + (t / s) • P) * (s • (1 : Square 3) + Q) - ρ • Q =
      (t / s) • ((s ^ 3 / t) • (1 : Square 3) + s • (P + Q) + P * Q) := by
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_smul, smul_add]
  match_scalars
  all_goals (field_simp [hs, ht] <;> first | ring | (rw [hst]; ring))

#print axioms determinant_lower_commuting
#assert_trust kernel determinant_lower_commuting
#print axioms final_schur_matrix
#assert_trust kernel final_schur_matrix

end
end NLA.SP15
