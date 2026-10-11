import NLA.RowDeletion.GaussianRadius
import Mathlib.Probability.Independence.Integration

/-! # Spherical projection moments and the Gaussian coupling

On the Gaussian probability space, put U = G / ‖G‖ and D = ‖G‖² / n.
Then n⟪b,U⟫² D = ⟪b,G⟫². Radius/direction independence and E D = 1
identify the spherical second moment, and the same factorization gives the
L¹ coupling error. The statements allow any projection vector b.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace NLA.RowDeletion

lemma memLp_gaussian_inner {n : ℕ} (b : Vector n) :
    MemLp (fun g ↦ inner ℝ b g) 2 (stdGaussian (Vector n)) := by
  simpa using
    (memLp_id_gaussianReal 2).comp_measurePreserving (measurePreserving_gaussian_inner b)

lemma integrable_gaussian_inner_sq {n : ℕ} (b : Vector n) :
    Integrable (fun g ↦ (inner ℝ b g) ^ 2) (stdGaussian (Vector n)) :=
  (memLp_gaussian_inner b).integrable_sq

lemma integral_gaussian_inner_sq {n : ℕ} (b : Vector n) :
    (∫ g, (inner ℝ b g) ^ 2 ∂stdGaussian (Vector n)) = ‖b‖ ^ 2 := by
  have h := variance_eq_sub (memLp_gaussian_inner b)
  simpa only [Pi.pow_apply, variance_gaussian_inner, integral_gaussian_inner, zero_pow (by decide : 2 ≠ 0),
    sub_zero] using h.symm

lemma integrable_spherical_projection_sq {n : ℕ} (hn : 0 < n) (b : Vector n) :
    Integrable (fun u ↦ (n : ℝ) * (inner ℝ b u) ^ 2) (sphericalLaw n) := by
  let := isProbabilityMeasure_sphericalLaw hn
  refine (integrable_const ((n : ℝ) * ‖b‖ ^ 2)).mono' (by fun_prop) ?_
  filter_upwards [ae_sphericalLaw_norm n] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hi := abs_real_inner_le_norm b u
  rw [hu, mul_one] at hi
  have hs := (sq_le_sq₀ (abs_nonneg (inner ℝ b u)) (norm_nonneg b)).2 hi
  rw [sq_abs] at hs
  exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)

lemma integrable_spherical_projection_sq_gaussian {n : ℕ} (hn : 0 < n) (b : Vector n) :
    Integrable (fun g ↦ (n : ℝ) * (inner ℝ b (sphereDirection g)) ^ 2)
      (stdGaussian (Vector n)) := by
  have h := integrable_spherical_projection_sq hn b
  rw [← stdGaussian_map_sphereDirection hn] at h
  exact h.comp_measurable (measurable_sphereDirection n)

lemma spherical_projection_sq_mul_radius {n : ℕ} (hn : 0 < n)
    (b g : Vector n) :
    ((n : ℝ) * (inner ℝ b (sphereDirection g)) ^ 2) * (‖g‖ ^ 2 / n) =
      (inner ℝ b g) ^ 2 := by
  have hi := congrArg (fun x ↦ inner ℝ b x) (norm_smul_sphereDirection g)
  simp only [inner_smul_right] at hi
  calc
    _ = (‖g‖ * inner ℝ b (sphereDirection g)) ^ 2 := by
      field_simp [show (n : ℝ) ≠ 0 by positivity]
    _ = _ := by rw [← hi]

/-- The scaled spherical projection has mean ‖b‖², also on the Gaussian coupling space. -/
theorem integral_spherical_projection_sq_gaussian {n : ℕ} (hn : 0 < n) (b : Vector n) :
    (∫ g, (n : ℝ) * (inner ℝ b (sphereDirection g)) ^ 2 ∂stdGaussian (Vector n)) =
      ‖b‖ ^ 2 := by
  have hi := (indepFun_sphereDirection_norm hn).comp
    (φ := fun u : Vector n ↦ (n : ℝ) * (inner ℝ b u) ^ 2)
    (ψ := fun r : ℝ ↦ r ^ 2 / n) (by fun_prop) (by fun_prop)
  have h := hi.integral_fun_mul_eq_mul_integral (by fun_prop) (by fun_prop)
  simpa only [Function.comp_def, spherical_projection_sq_mul_radius hn,
    integral_gaussian_inner_sq, integral_gaussian_normalized_norm_sq hn, mul_one] using h.symm

/-- Spherical isotropy in the normalization used by the row-deletion estimates. -/
theorem integral_spherical_projection_sq {n : ℕ} (hn : 0 < n) (b : Vector n) :
    (∫ u, (n : ℝ) * (inner ℝ b u) ^ 2 ∂sphericalLaw n) = ‖b‖ ^ 2 := by
  rw [← stdGaussian_map_sphereDirection hn, integral_map (by fun_prop) (by fun_prop)]
  exact integral_spherical_projection_sq_gaussian hn b

/-- Exact factorization of the L¹ error; only its radial factor needs estimating. -/
theorem integral_abs_spherical_projection_sq_sub_gaussian_eq {n : ℕ}
    (hn : 0 < n) (b : Vector n) :
    (∫ g, |(n : ℝ) * (inner ℝ b (sphereDirection g)) ^ 2 - (inner ℝ b g) ^ 2|
      ∂stdGaussian (Vector n)) =
        ‖b‖ ^ 2 * ∫ g : Vector n, |‖g‖ ^ 2 / n - 1| ∂stdGaussian (Vector n) := by
  have he (g : Vector n) :
      |(n : ℝ) * (inner ℝ b (sphereDirection g)) ^ 2 - (inner ℝ b g) ^ 2| =
        ((n : ℝ) * (inner ℝ b (sphereDirection g)) ^ 2) * |1 - ‖g‖ ^ 2 / n| := by
    rw [← spherical_projection_sq_mul_radius hn b g]
    rw [show (n : ℝ) * (inner ℝ b (sphereDirection g)) ^ 2 -
        ((n : ℝ) * (inner ℝ b (sphereDirection g)) ^ 2) * (‖g‖ ^ 2 / n) =
        ((n : ℝ) * (inner ℝ b (sphereDirection g)) ^ 2) * (1 - ‖g‖ ^ 2 / n) by ring,
      abs_mul, abs_of_nonneg (by positivity)]
  simp_rw [he]
  have hi := (indepFun_sphereDirection_norm hn).comp
    (φ := fun u : Vector n ↦ (n : ℝ) * (inner ℝ b u) ^ 2)
    (ψ := fun r : ℝ ↦ |1 - r ^ 2 / n|) (by fun_prop) (by fun_prop)
  have h := hi.integral_fun_mul_eq_mul_integral (by fun_prop) (by fun_prop)
  simpa only [Function.comp_def, integral_spherical_projection_sq_gaussian hn,
    abs_sub_comm (1 : ℝ)] using h

/-- The Gaussian/spherical projection coupling error is at most ‖b‖² sqrt(2/n). -/
theorem integral_abs_spherical_projection_sq_sub_gaussian_le {n : ℕ}
    (hn : 0 < n) (b : Vector n) :
    (∫ g, |(n : ℝ) * (inner ℝ b (sphereDirection g)) ^ 2 - (inner ℝ b g) ^ 2|
      ∂stdGaussian (Vector n)) ≤ ‖b‖ ^ 2 * Real.sqrt (2 / n) := by
  rw [integral_abs_spherical_projection_sq_sub_gaussian_eq hn]
  exact mul_le_mul_of_nonneg_left
    (integral_abs_gaussian_normalized_norm_sq_sub_one_le hn) (sq_nonneg ‖b‖)

end NLA.RowDeletion
