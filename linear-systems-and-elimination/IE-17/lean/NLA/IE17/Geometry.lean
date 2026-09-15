/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.IE17.Norms

noncomputable section
open Matrix
open scoped InnerProductSpace
namespace NLA.IE17

lemma inner_eq_sum {n : ℕ} (u v : Vec n) : ⟪u, v⟫_ℝ = ∑ i, u i * v i := by
  simp only [PiLp.inner_apply, Real.inner_apply]

lemma transpose_inner {m n : ℕ} (A : Mat m n) (u : Vec m) (x : Vec n) :
    ⟪A.transpose.toEuclideanLin u, x⟫_ℝ = ⟪u, A.toEuclideanLin x⟫_ℝ := by
  simp only [inner_eq_sum, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma add_matrix_apply {m n : ℕ} (A E : Mat m n) (x : Vec n) :
    (A + E).toEuclideanLin x = A.toEuclideanLin x + E.toEuclideanLin x := by
  simp

lemma residual_sub_perturbation {m n : ℕ} (A E : Mat m n) (b : Vec m) (x : Vec n) :
    residual (A + E) b x = residual A b x - E.toEuclideanLin x := by
  simp [residual, sub_add_eq_sub_sub]

lemma apply_norm_sq_le {m n : ℕ} (E : Mat m n) (x : Vec n) :
    ‖E.toEuclideanLin x‖ ^ 2 ≤ spectralNorm E ^ 2 * ‖x‖ ^ 2 := by
  simpa only [mul_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (apply_norm_le E x) 2

lemma transpose_apply_norm_sq_le {m n : ℕ} (E : Mat m n) (u : Vec m) :
    ‖E.transpose.toEuclideanLin u‖ ^ 2 ≤ spectralNorm E ^ 2 * ‖u‖ ^ 2 := by
  simpa only [spectralNorm_transpose] using apply_norm_sq_le E.transpose u

lemma spectralNorm_sq_le_of_forall {m n : ℕ} (E : Mat m n) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y : Vec n, ‖E.toEuclideanLin y‖ ^ 2 ≤ c * ‖y‖ ^ 2) :
    spectralNorm E ^ 2 ≤ c := by
  have hE : spectralNorm E ≤ Real.sqrt c := by
    apply (spectralNorm_le_iff E (Real.sqrt_nonneg c)).mpr
    intro y
    have hsq := h y
    have hsqrt : (Real.sqrt c * ‖y‖) ^ 2 = c * ‖y‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc]
    have hprod : 0 ≤ Real.sqrt c * ‖y‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    nlinarith [sq_nonneg (‖E.toEuclideanLin y‖ - Real.sqrt c * ‖y‖)]
  nlinarith [spectralNorm_nonneg E, Real.sq_sqrt hc, Real.sqrt_nonneg c]

end NLA.IE17
