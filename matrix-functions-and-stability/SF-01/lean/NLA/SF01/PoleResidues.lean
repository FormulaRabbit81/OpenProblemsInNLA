/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Exact residue normalization for every supplied orthogonal diagonalization.
The nonnegative-weight theorem deliberately does not assume ValidData.
-/
import NLA.SF01.PoleDiagonalization
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma poleMatrix_first_column (d : RidgeData) (i : Fin (d.size + 1)) :
    poleMatrix d i 0 = d.b⁻¹ * poleVector d i * Real.sqrt d.a := by
  by_cases hi : i = 0
  · subst i
    simp [poleMatrix, poleOffsets, poleVector, mul_assoc]
  · simp [poleMatrix, Matrix.diagonal_apply, hi, poleOffsets, poleVector, mul_assoc]

lemma pole_auxiliary_solve (d : RidgeData) (hd : ValidData d) :
    poleMatrix d *ᵥ Pi.single (0 : Fin (d.size + 1)) (d.b / Real.sqrt d.a) =
      poleVector d := by
  funext i
  change (poleMatrix d i) ⬝ᵥ Pi.single (0 : Fin (d.size + 1))
    (d.b / Real.sqrt d.a) = poleVector d i
  rw [dotProduct_single, poleMatrix_first_column]
  have ha : Real.sqrt d.a ≠ 0 := (Real.sqrt_pos.mpr hd.1).ne'
  have hb : d.b ≠ 0 := hd.2.1.ne'
  field_simp [ha, hb] <;> ring

lemma pole_auxiliary_dot (d : RidgeData) (hd : ValidData d) :
    poleVector d ⬝ᵥ Pi.single (0 : Fin (d.size + 1)) (d.b / Real.sqrt d.a) = d.b := by
  rw [dotProduct_single]
  change Real.sqrt d.a * (d.b / Real.sqrt d.a) = d.b
  have ha : Real.sqrt d.a ≠ 0 := (Real.sqrt_pos.mpr hd.1).ne'
  field_simp [ha] <;> ring

lemma pole_diagonalized_solve (d : RidgeData)
    (Q : Square (d.size + 1)) (lam : Fin (d.size + 1) → ℝ)
    (hdiag : PoleDiagonalization d Q lam) (v : Vector (d.size + 1))
    (hv : poleMatrix d *ᵥ v = poleVector d) :
    ∀ i, lam i * (Q.transpose *ᵥ v) i = spectralCoordinates d Q i := by
  have hm : Matrix.diagonal lam *ᵥ (Q.transpose *ᵥ v) =
      Q.transpose *ᵥ poleVector d := by
    calc
      Matrix.diagonal lam *ᵥ (Q.transpose *ᵥ v) =
          (Q.transpose * Q) *ᵥ (Matrix.diagonal lam *ᵥ (Q.transpose *ᵥ v)) := by
        rw [hdiag.1.1, Matrix.one_mulVec]
      _ = Q.transpose *ᵥ ((Q * Matrix.diagonal lam * Q.transpose) *ᵥ v) := by
        simp only [Matrix.mulVec_mulVec, mul_assoc]
      _ = Q.transpose *ᵥ poleVector d := by rw [← hdiag.2.2, hv]
  intro i
  simpa only [Matrix.mulVec_diagonal, spectralCoordinates] using congrFun hm i

theorem pole_residue_normalization (d : RidgeData) (hd : ValidData d)
    (Q : Square (d.size + 1)) (lam : Fin (d.size + 1) → ℝ)
    (hdiag : PoleDiagonalization d Q lam) :
    ∑ i : Fin (d.size + 1), spectralCoordinates d Q i ^ 2 / lam i = d.b := by
  let v : Vector (d.size + 1) := Pi.single 0 (d.b / Real.sqrt d.a)
  have hv : poleMatrix d *ᵥ v = poleVector d := pole_auxiliary_solve d hd
  have hcoord := pole_diagonalized_solve d Q lam hdiag v hv
  have hterm : ∀ i, spectralCoordinates d Q i ^ 2 / lam i =
      spectralCoordinates d Q i * (Q.transpose *ᵥ v) i := by
    intro i
    apply (div_eq_iff (hdiag.2.1 i).ne').mpr
    rw [← hcoord i]
    ring
  calc
    (∑ i : Fin (d.size + 1), spectralCoordinates d Q i ^ 2 / lam i) =
        ∑ i : Fin (d.size + 1), spectralCoordinates d Q i * (Q.transpose *ᵥ v) i :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (Q.transpose *ᵥ poleVector d) ⬝ᵥ (Q.transpose *ᵥ v) := rfl
    _ = poleVector d ⬝ᵥ v := orthogonal_transpose_dot Q hdiag.1 _ _
    _ = d.b := pole_auxiliary_dot d hd

theorem reciprocal_weights_nonnegative (d : RidgeData)
    (Q : Square (d.size + 1)) (lam : Fin (d.size + 1) → ℝ)
    (hlam : ∀ i, 0 < lam i) :
    ∀ i, 0 ≤ reciprocalWeights d Q lam i := by
  intro i
  exact div_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (hlam i).le)

lemma reciprocalWeights_sum (d : RidgeData) (hd : ValidData d)
    (Q : Square (d.size + 1)) (lam : Fin (d.size + 1) → ℝ)
    (hdiag : PoleDiagonalization d Q lam) :
    ∑ i : Fin (d.size + 1), reciprocalWeights d Q lam i = d.b⁻¹ := by
  calc
    (∑ i : Fin (d.size + 1), reciprocalWeights d Q lam i) =
        (∑ i : Fin (d.size + 1), spectralCoordinates d Q i ^ 2 / lam i) / d.b ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      unfold reciprocalWeights
      field_simp [hd.2.1.ne', (hdiag.2.1 i).ne'] <;> ring
    _ = d.b⁻¹ := by
      rw [pole_residue_normalization d hd Q lam hdiag]
      field_simp [hd.2.1.ne'] <;> ring

end
end NLA.SF01
