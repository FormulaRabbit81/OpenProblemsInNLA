/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.IE17.Geometry

noncomputable section
open Matrix
open scoped InnerProductSpace
namespace NLA.IE17

/-- A nonzero least-squares residual is the projection of b onto its own unit direction. -/
lemma feasible_residual_direction {m n : ℕ} {A E : Mat m n} {b : Vec m} {x : Vec n}
    (hE : Feasible A b x E) (hq : residual (A + E) b x ≠ 0) :
    ∃ u : Vec m, ‖u‖ = 1 ∧
      (A + E).transpose.toEuclideanLin u = 0 ∧
      residual (A + E) b x = ⟪u, b⟫_ℝ • u := by
  let q := residual (A + E) b x
  let u : Vec m := ‖q‖⁻¹ • q
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hT : (A + E).transpose.toEuclideanLin q = 0 := hE
  have hqx : ⟪q, (A + E).toEuclideanLin x⟫_ℝ = 0 := by
    rw [← transpose_inner, hT, inner_zero_left]
  have hb : b = q + (A + E).toEuclideanLin x := by
    dsimp [q, residual]
    abel
  have hqb : ⟪q, b⟫_ℝ = ‖q‖ ^ 2 := by
    rw [hb, inner_add_right, real_inner_self_eq_norm_sq, hqx, add_zero]
  have hub : ⟪u, b⟫_ℝ = ‖q‖ := by
    simp only [u, inner_smul_left, RCLike.conj_to_real, hqb]
    field_simp
  refine ⟨u, ?_, ?_, ?_⟩
  · simp [u, norm_smul, hn]
  · change (A + E).transpose.toEuclideanLin (‖q‖⁻¹ • q) = 0
    rw [map_smul, hT, smul_zero]
  · change q = ⟪u, b⟫_ℝ • u
    rw [hub]
    simp [u, smul_smul, hn]

lemma perturbation_transpose_on_direction {m n : ℕ} {A E : Mat m n} {u : Vec m}
    (h : (A + E).transpose.toEuclideanLin u = 0) :
    E.transpose.toEuclideanLin u = -A.transpose.toEuclideanLin u := by
  have heq : A.transpose.toEuclideanLin u + E.transpose.toEuclideanLin u = 0 := by
    simpa using h
  exact eq_neg_of_add_eq_zero_right heq

/-- Exact identity behind D, with the same unit direction used for the normal equation. -/
lemma residual_projection_sq {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n)
    (u : Vec m) (hu : ‖u‖ = 1) :
    ‖residual A b x - ⟪u, b⟫_ℝ • u‖ ^ 2 =
      ‖residual A b x‖ ^ 2 - ⟪u, residual A b x⟫_ℝ ^ 2 +
        ⟪u, A.toEuclideanLin x⟫_ℝ ^ 2 := by
  have hb : ⟪u, b⟫_ℝ = ⟪u, residual A b x⟫_ℝ + ⟪u, A.toEuclideanLin x⟫_ℝ := by
    rw [← inner_add_right]
    congr 1
    simp [residual]
  rw [norm_sub_sq_real, inner_smul_right, real_inner_comm u (residual A b x), norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, hu]
  rw [hb]
  ring

/-- The nonzero-new-residual branch bounds both quadratic forms by the actual operator norm. -/
lemma feasible_direction_bounds {m n : ℕ} {A E : Mat m n} {b : Vec m} {x : Vec n}
    (hE : Feasible A b x E) (hq : residual (A + E) b x ≠ 0) :
    ∃ u : Vec m, ‖u‖ = 1 ∧
      ‖A.transpose.toEuclideanLin u‖ ^ 2 ≤ spectralNorm E ^ 2 ∧
      ‖residual A b x‖ ^ 2 - ⟪u, residual A b x⟫_ℝ ^ 2 +
        ⟪u, A.toEuclideanLin x⟫_ℝ ^ 2 ≤ spectralNorm E ^ 2 * ‖x‖ ^ 2 := by
  obtain ⟨u, hu, hT, hqeq⟩ := feasible_residual_direction hE hq
  refine ⟨u, hu, ?_, ?_⟩
  · have hbound := transpose_apply_norm_sq_le E u
    rw [perturbation_transpose_on_direction hT, norm_neg, hu] at hbound
    simpa using hbound
  · have hEx : E.toEuclideanLin x = residual A b x - ⟪u, b⟫_ℝ • u := by
      rw [← hqeq, residual_sub_perturbation]
      abel
    have hbound := apply_norm_sq_le E x
    rw [hEx, residual_projection_sq A b x u hu] at hbound
    exact hbound

/-- In the consistent perturbed branch, the same genuine operator norm still controls r. -/
lemma feasible_zero_residual_bound {m n : ℕ} {A E : Mat m n} {b : Vec m} {x : Vec n}
    (hq : residual (A + E) b x = 0) :
    ‖residual A b x‖ ^ 2 ≤ spectralNorm E ^ 2 * ‖x‖ ^ 2 := by
  have hEx : E.toEuclideanLin x = residual A b x := by
    have h := hq
    rw [residual_sub_perturbation, sub_eq_zero] at h
    exact h.symm
  simpa only [hEx] using apply_norm_sq_le E x

end NLA.IE17
