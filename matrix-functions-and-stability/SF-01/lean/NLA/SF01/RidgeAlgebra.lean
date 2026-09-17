/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, Cambridge DAMTP.

Finite rational algebra with actual matrix inverse hypotheses. No pole or
weight division, spectral approximation, or interval computation is used.
-/
import NLA.SF01.ResolventDomination
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Commute

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma shifted_right_resolvent {n : ℕ} (A : Square n) (t : ℝ)
    (hunit : IsUnit (shifted A t)) :
    A * (shifted A t)⁻¹ = 1 - t • (shifted A t)⁻¹ := by
  apply eq_sub_iff_add_eq.mpr
  have h := Matrix.mul_nonsing_inv (shifted A t)
    ((Matrix.isUnit_iff_isUnit_det (shifted A t)).mp hunit)
  simpa only [shifted, Matrix.add_mul, Matrix.smul_mul, one_mul] using h

lemma shifted_left_resolvent {n : ℕ} (A : Square n) (t : ℝ)
    (hunit : IsUnit (shifted A t)) :
    (shifted A t)⁻¹ * A = 1 - t • (shifted A t)⁻¹ := by
  apply eq_sub_iff_add_eq.mpr
  have h := Matrix.nonsing_inv_mul (shifted A t)
    ((Matrix.isUnit_iff_isUnit_det (shifted A t)).mp hunit)
  simpa only [shifted, Matrix.mul_add, Matrix.mul_smul, mul_one] using h

lemma shifted_inverse_commutation {n : ℕ} (A : Square n) (t : ℝ)
    (hunit : IsUnit (shifted A t)) :
    A * (shifted A t)⁻¹ = (shifted A t)⁻¹ * A := by
  exact (shifted_right_resolvent A t hunit).trans
    (shifted_left_resolvent A t hunit).symm

lemma ridgeEval_apply {n : ℕ} (d : RidgeData) (A : Square n) (i j : Fin n) :
    ridgeEval d A i j = d.a * (1 : Square n) i j + d.b * A i j +
      ∑ k : Fin d.size, d.weights k * (A * (shifted A (d.poles k))⁻¹) i j := by
  simp only [ridgeEval, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]

lemma ridgeEval_mulVec_apply {n : ℕ} (d : RidgeData) (A : Square n)
    (v : Vector n) (i : Fin n) :
    (ridgeEval d A *ᵥ v) i = d.a * v i + d.b * (A *ᵥ v) i +
      ∑ k : Fin d.size, d.weights k * ((A * (shifted A (d.poles k))⁻¹) *ᵥ v) i := by
  simp only [ridgeEval, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.sum_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]

theorem ridge_commutes (d : RidgeData) (hd : ValidData d)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A) :
    Commute A (ridgeEval d A) := by
  have ha : Commute A (d.a • (1 : Square n)) := by
    change A * (d.a • (1 : Square n)) = (d.a • (1 : Square n)) * A
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
  have hb : Commute A (d.b • A) := by
    change A * (d.b • A) = (d.b • A) * A
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hparts : ∀ k : Fin d.size,
      Commute A (d.weights k • (A * (shifted A (d.poles k))⁻¹)) := by
    intro k
    have hu := (H_shift_structure hn A hA (d.poles k) (hd.2.2.1 k).le).2.1
    have he := shifted_inverse_commutation A (d.poles k) hu
    change A * (d.weights k • (A * (shifted A (d.poles k))⁻¹)) =
      (d.weights k • (A * (shifted A (d.poles k))⁻¹)) * A
    rw [Matrix.mul_smul, Matrix.smul_mul]
    apply congrArg (fun X : Square n => d.weights k • X)
    calc
      A * (A * (shifted A (d.poles k))⁻¹) =
          A * ((shifted A (d.poles k))⁻¹ * A) := congrArg (fun X => A * X) he
      _ = (A * (shifted A (d.poles k))⁻¹) * A := (mul_assoc _ _ _).symm
  exact (ha.add_right hb).add_right
    (Commute.sum_right Finset.univ
      (fun k => d.weights k • (A * (shifted A (d.poles k))⁻¹)) A (fun k _ => hparts k))

end
end NLA.SF01
