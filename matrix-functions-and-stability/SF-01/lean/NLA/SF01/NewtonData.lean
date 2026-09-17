/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Uniform scalar data are selected before the matrix dimension and matrix.
The existing kernel LeanCert half certificate is consumed in coefficient halving.
-/
import NLA.SF01.ReciprocalIdentity
import NLA.SF01.Numerical

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

def nextRidgeData (d : RidgeData) (Q : Square (d.size + 1))
    (lam : Fin (d.size + 1) → ℝ) : RidgeData where
  size := d.size + (d.size + 1)
  a := d.a / 2
  b := d.b / 2
  poles := Fin.addCases d.poles lam
  weights := Fin.addCases (fun j => d.weights j / 2)
    (fun i => reciprocalWeights d Q lam i / 2)

lemma nextRidgeData_valid (d : RidgeData) (hd : ValidData d)
    (Q : Square (d.size + 1)) (lam : Fin (d.size + 1) → ℝ)
    (hlam : ∀ i, 0 < lam i) :
    ValidData (nextRidgeData d Q lam) := by
  refine ⟨half_coefficient_positive d.a hd.1,
    half_coefficient_positive d.b hd.2.1, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [nextRidgeData, Fin.addCases_left] using hd.2.2.1 j
    · simpa only [nextRidgeData, Fin.addCases_right] using hlam j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [nextRidgeData, Fin.addCases_left] using
        div_nonneg (hd.2.2.2 j) (show (0 : ℝ) ≤ 2 by norm_num)
    · simpa only [nextRidgeData, Fin.addCases_right] using
        div_nonneg (reciprocal_weights_nonnegative d Q lam hlam j)
          (show (0 : ℝ) ≤ 2 by norm_num)

lemma nextRidgeData_eval {n : ℕ} (d : RidgeData)
    (Q : Square (d.size + 1)) (lam : Fin (d.size + 1) → ℝ) (A : Square n) :
    ridgeEval (nextRidgeData d Q lam) A =
      (1 / 2 : ℝ) • (ridgeEval d A + reciprocalEval d Q lam A) := by
  have hsum (m : ℕ) (w : Fin m → ℝ) (F : Fin m → Square n) :
      (∑ j : Fin m, (w j / 2) • F j) =
        (1 / 2 : ℝ) • ∑ j : Fin m, w j • F j := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    congr 1
    ring
  dsimp only [ridgeEval, nextRidgeData, reciprocalEval]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [hsum, hsum]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem newton_data_step (d : RidgeData) (hd : ValidData d) :
    ∃ d' : RidgeData, ValidData d' ∧ d'.a = d.a / 2 ∧ d'.b = d.b / 2 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ A : Square n, Admissible A →
        ridgeEval d' A = (1 / 2 : ℝ) • (ridgeEval d A + (ridgeEval d A)⁻¹ * A) := by
  obtain ⟨Q, lam, hdiag⟩ := pole_diagonalization_exists d hd
  refine ⟨nextRidgeData d Q lam, nextRidgeData_valid d hd Q lam hdiag.2.1,
    rfl, rfl, ?_⟩
  intro n hn A hA
  rw [nextRidgeData_eval, matrix_reciprocal_identity d hd Q lam hdiag hn A hA]

end
end NLA.SF01
