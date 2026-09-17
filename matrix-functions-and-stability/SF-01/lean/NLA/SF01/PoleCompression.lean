/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

A finite rank update using actual unit matrices and rectangular lift factors.
No inverse cancellation occurs without its proved unit hypothesis.
-/
import NLA.SF01.RidgeCompression

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma pole_inverse_scalarLift (d : RidgeData) (hd : ValidData d)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A) :
    (poleBlock d A)⁻¹ * scalarLift (n := n) (poleVector d) =
      d.b • ((baseBlock d A)⁻¹ * scalarLift (n := n) (poleVector d) *
        (compressedFactor d A)⁻¹) := by
  let U := scalarLift (n := n) (poleVector d)
  let B0 := baseBlock d A
  let Bp := poleBlock d A
  let K := baseCompression d A
  let F := compressedFactor d A
  have hu := reciprocal_blocks_isUnit d hd hn A hA
  have hF := (compressedFactor_structure d hd hn A hA).1
  have hB0 : B0 * B0⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu.1)
  have hBp : Bp⁻¹ * Bp = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu.2)
  have hFF : F * F⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hF)
  have hbase : B0 * (B0⁻¹ * U) = U := by
    rw [← Matrix.mul_assoc, hB0, Matrix.one_mul]
  have houter : (U * U.transpose) * (B0⁻¹ * U) = U * K := by
    simp only [K, baseCompression, U, B0, Matrix.mul_assoc]
  have hscalar : d.b⁻¹ • (U * F) = U + d.b⁻¹ • (U * K) := by
    dsimp only [F, compressedFactor, K]
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, smul_add,
      smul_smul, inv_mul_cancel₀ hd.2.1.ne', one_smul]
  have hstep : Bp * (B0⁻¹ * U) = d.b⁻¹ • (U * F) := by
    calc
      Bp * (B0⁻¹ * U) =
          B0 * (B0⁻¹ * U) + d.b⁻¹ • ((U * U.transpose) * (B0⁻¹ * U)) := by
        change poleBlock d A * (B0⁻¹ * U) = _
        rw [poleBlock_rank_update, Matrix.add_mul, Matrix.smul_mul]
      _ = U + d.b⁻¹ • (U * K) := by rw [hbase, houter]
      _ = d.b⁻¹ • (U * F) := hscalar.symm
  change Bp⁻¹ * U = d.b • (B0⁻¹ * U * F⁻¹)
  calc
    Bp⁻¹ * U = d.b • (Bp⁻¹ * (d.b⁻¹ • (U * F)) * F⁻¹) := by
      symm
      rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul,
        mul_inv_cancel₀ hd.2.1.ne', one_smul]
      simp only [Matrix.mul_assoc, hFF, Matrix.mul_one]
    _ = d.b • (Bp⁻¹ * (Bp * (B0⁻¹ * U)) * F⁻¹) := by rw [← hstep]
    _ = d.b • (B0⁻¹ * U * F⁻¹) := by
      rw [← Matrix.mul_assoc Bp⁻¹ Bp, hBp, Matrix.one_mul]

lemma poleCompression_factor (d : RidgeData) (hd : ValidData d)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A) :
    poleCompression d A =
      d.b • (baseCompression d A * (compressedFactor d A)⁻¹) := by
  unfold poleCompression
  rw [Matrix.mul_assoc, pole_inverse_scalarLift d hd hn A hA, Matrix.mul_smul]
  simp only [baseCompression, Matrix.mul_assoc]

lemma compressedFactor_inverse_complement (d : RidgeData) (hd : ValidData d)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A) :
    (compressedFactor d A)⁻¹ =
      d.b⁻¹ • (1 : Square n) - (d.b⁻¹) ^ 2 • poleCompression d A := by
  have hF := (compressedFactor_structure d hd hn A hA).1
  have hf : d.b • (compressedFactor d A)⁻¹ +
      baseCompression d A * (compressedFactor d A)⁻¹ = 1 := by
    have h := Matrix.mul_nonsing_inv (compressedFactor d A)
      ((Matrix.isUnit_iff_isUnit_det _).mp hF)
    simpa only [compressedFactor, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] using h
  have hm := congrArg (fun T : Square n => d.b⁻¹ • T) hf
  simp only [smul_add, smul_smul, inv_mul_cancel₀ hd.2.1.ne', one_smul] at hm
  have hscalar : (d.b⁻¹) ^ 2 * d.b = d.b⁻¹ := by
    field_simp [hd.2.1.ne'] <;> ring
  rw [poleCompression_factor d hd hn A hA, smul_smul, hscalar]
  exact eq_sub_iff_add_eq.mpr hm

lemma poleCompression_spectral (d : RidgeData) (hd : ValidData d)
    (Q : Square (d.size + 1)) (lam : Fin (d.size + 1) → ℝ)
    (hdiag : PoleDiagonalization d Q lam)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A) :
    poleCompression d A = ∑ i : Fin (d.size + 1),
      spectralCoordinates d Q i ^ 2 • (shifted A (lam i))⁻¹ := by
  let U := scalarLift (n := n) (poleVector d)
  let V := matrixLift (n := n) Q
  let E := blockFamily (fun i => (shifted A (lam i))⁻¹)
  have hcompression : U.transpose * (V * E * V.transpose) * U =
      (V.transpose * U).transpose * E * (V.transpose * U) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  calc
    poleCompression d A = U.transpose * (V * E * V.transpose) * U := by
      unfold poleCompression
      rw [poleBlock_inverse_diagonalized d hd Q lam hdiag hn A hA]
    _ = (V.transpose * U).transpose * E * (V.transpose * U) := hcompression
    _ = ∑ i : Fin (d.size + 1),
        spectralCoordinates d Q i ^ 2 • (shifted A (lam i))⁻¹ := by
      dsimp only [V, U, E]
      simpa only [matrixLift_transpose_scalarLift, spectralCoordinates] using
        scalarLift_blockFamily_compression (Q.transpose *ᵥ poleVector d)
          (fun i => (shifted A (lam i))⁻¹)

end
end NLA.SF01
