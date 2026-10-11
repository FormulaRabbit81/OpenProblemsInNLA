import NLA.RowDeletion.GaussianTrimming
import NLA.RowDeletion.ExponentialComparison

/-! # Exponential moments of a squared standard real Gaussian

The proof is a single Gaussian integral, with no moment series. Together with
`integral_exp_le_integral_exp_independent_mul`, it is the scalar input for the
spherical covariance concentration argument.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace NLA.RowDeletion

theorem integral_exp_gaussian_sq {t : ℝ} (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  have hb : 0 < 1 / 2 - t := by linarith
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have he : (fun x : ℝ ↦ gaussianPDFReal 0 1 x • Real.exp (t * x ^ 2)) =
      fun x ↦ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he, integral_const_mul, integral_gaussian, ← Real.sqrt_inv,
    ← Real.sqrt_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹), ← Real.sqrt_inv]
  congr 1
  field_simp

theorem integrable_exp_gaussian_sq {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  by_contra h
  have he := integral_exp_gaussian_sq ht
  rw [integral_undef h] at he
  have hp : 0 < (Real.sqrt (1 - 2 * t))⁻¹ := by
    have : 0 < 1 - 2 * t := by linarith
    positivity
  linarith

theorem integral_exp_centered_gaussian_sq {t : ℝ} (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * (x ^ 2 - 1)) ∂gaussianReal 0 1) =
      Real.exp (-t) * (Real.sqrt (1 - 2 * t))⁻¹ := by
  simp_rw [mul_sub, mul_one, Real.exp_sub, div_eq_mul_inv, mul_comm _ (Real.exp t)⁻¹]
  rw [integral_const_mul, integral_exp_gaussian_sq ht, Real.exp_neg]

/-- A scalar logarithm inequality supplies the source's MGF bound, with no
power-series expansion. The estimate even holds for all negative parameters. -/
theorem integral_exp_centered_gaussian_sq_le {t : ℝ} (ht : t ≤ 1 / 8) :
    (∫ x : ℝ, Real.exp (t * (x ^ 2 - 1)) ∂gaussianReal 0 1) ≤
      Real.exp (32 * t ^ 2) := by
  have hd : 0 < 1 - 2 * t := by linarith
  rw [integral_exp_centered_gaussian_sq (by linarith)]
  apply Real.le_exp_of_log_le
  rw [Real.log_mul (Real.exp_ne_zero _) (inv_ne_zero (Real.sqrt_pos.mpr hd).ne'),
    Real.log_exp, Real.log_inv, Real.log_sqrt hd.le]
  have hlog := Real.one_sub_inv_le_log_of_pos hd
  have he : -t - (1 - (1 - 2 * t)⁻¹) / 2 = 2 * t ^ 2 / (1 - 2 * t) := by
    field_simp [hd.ne', (by linarith : 1 - t * 2 ≠ 0)]
    ring
  have hbound : 2 * t ^ 2 / (1 - 2 * t) ≤ 32 * t ^ 2 := by
    apply (div_le_iff₀ hd).mpr
    have := mul_le_mul_of_nonneg_right ht (sq_nonneg t)
    nlinarith [sq_nonneg t]
  linarith

end NLA.RowDeletion
