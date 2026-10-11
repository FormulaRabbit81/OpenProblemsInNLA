import NLA.RowDeletion.GaussianMoments
import NLA.RowDeletion.GaussianSphere

/-! # Gaussian radius moments

The squared norm is the sum of independent squared standard real Gaussians.
The moments are derived from this representation without introducing a
chi-square distribution or computing a radial density integral.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NLA.RowDeletion

lemma memLp_gaussian_norm_sq (n : ℕ) :
    MemLp (fun g : Vector n ↦ ‖g‖ ^ 2) 2 (stdGaussian (Vector n)) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  convert! (IsGaussian.memLp_id (stdGaussian (Vector n)) 4 (by norm_num)).integrable_norm_pow
    (by norm_num : (4 : ℕ) ≠ 0) using 1
  funext x
  simp [← pow_mul]

lemma integrable_gaussian_norm_sq (n : ℕ) :
    Integrable (fun g : Vector n ↦ ‖g‖ ^ 2) (stdGaussian (Vector n)) :=
  (memLp_gaussian_norm_sq n).integrable (by norm_num)

theorem integral_gaussian_norm_sq (n : ℕ) :
    (∫ g : Vector n, ‖g‖ ^ 2 ∂stdGaussian (Vector n)) = n := by
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [EuclideanSpace.real_norm_sq_eq]
  change (∫ x : Fin n → ℝ, ∑ i, x i ^ 2 ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) = _
  rw [integral_finsetSum]
  · simp_rw [integral_comp_eval (μ := fun _ : Fin n ↦ gaussianReal 0 1)
      (f := fun x : ℝ ↦ x ^ 2) (by fun_prop), integral_gaussian_sq]
    simp
  · intro i _
    exact integrable_comp_eval (μ := fun _ : Fin n ↦ gaussianReal 0 1)
      (i := i) integrable_gaussian_sq

theorem variance_gaussian_norm_sq (n : ℕ) :
    Var[fun g : Vector n ↦ ‖g‖ ^ 2; stdGaussian (Vector n)] = 2 * n := by
  rw [← map_pi_eq_stdGaussian, variance_map (by fun_prop) (by fun_prop)]
  have he : (fun g : Vector n ↦ ‖g‖ ^ 2) ∘ WithLp.toLp 2 =
      ∑ i : Fin n, (fun x : Fin n → ℝ ↦ x i ^ 2) := by
    funext x
    simp [EuclideanSpace.real_norm_sq_eq]
  rw [he, variance_sum_pi (fun _ ↦ memLp_gaussian_sq)]
  simp [variance_gaussian_sq, mul_comm]

lemma integrable_gaussian_norm_fourth (n : ℕ) :
    Integrable (fun g : Vector n ↦ ‖g‖ ^ 4) (stdGaussian (Vector n)) := by
  convert! (memLp_gaussian_norm_sq n).integrable_sq using 1
  funext x
  ring

theorem integral_gaussian_norm_fourth (n : ℕ) :
    (∫ g : Vector n, ‖g‖ ^ 4 ∂stdGaussian (Vector n)) = (n : ℝ) * (n + 2) := by
  have h := variance_eq_sub (memLp_gaussian_norm_sq n)
  rw [variance_gaussian_norm_sq, integral_gaussian_norm_sq] at h
  change 2 * (n : ℝ) = (∫ g : Vector n, (‖g‖ ^ 2) ^ 2 ∂stdGaussian (Vector n)) - n ^ 2 at h
  simp only [← pow_mul] at h
  nlinarith

lemma memLp_gaussian_normalized_norm_sq (n : ℕ) :
    MemLp (fun g : Vector n ↦ ‖g‖ ^ 2 / n) 2 (stdGaussian (Vector n)) := by
  simpa only [div_eq_mul_inv] using (memLp_gaussian_norm_sq n).mul_const (n : ℝ)⁻¹

theorem integral_gaussian_normalized_norm_sq {n : ℕ} (hn : 0 < n) :
    (∫ g : Vector n, ‖g‖ ^ 2 / n ∂stdGaussian (Vector n)) = 1 := by
  rw [integral_div, integral_gaussian_norm_sq, div_self (by positivity : (n : ℝ) ≠ 0)]

theorem variance_gaussian_normalized_norm_sq {n : ℕ} (hn : 0 < n) :
    Var[fun g : Vector n ↦ ‖g‖ ^ 2 / n; stdGaussian (Vector n)] = (2 : ℝ) / n := by
  simp_rw [div_eq_mul_inv]
  rw [variance_mul_const, variance_gaussian_norm_sq]
  field_simp

theorem integral_gaussian_normalized_norm_sq_deviation_sq {n : ℕ} (hn : 0 < n) :
    (∫ g : Vector n, (‖g‖ ^ 2 / n - 1) ^ 2 ∂stdGaussian (Vector n)) = (2 : ℝ) / n := by
  have h := variance_eq_integral (μ := stdGaussian (Vector n))
    (X := fun g : Vector n ↦ ‖g‖ ^ 2 / n) (by fun_prop)
  rw [variance_gaussian_normalized_norm_sq hn, integral_gaussian_normalized_norm_sq hn] at h
  exact h.symm

/-- The radius factor in the spherical/Gaussian coupling converges in L¹.
Nonnegativity of variance gives the required L¹/L² comparison. -/
theorem integral_abs_gaussian_normalized_norm_sq_sub_one_le {n : ℕ} (hn : 0 < n) :
    (∫ g : Vector n, |‖g‖ ^ 2 / n - 1| ∂stdGaussian (Vector n)) ≤ Real.sqrt (2 / n) := by
  have hD : MemLp (fun g : Vector n ↦ ‖g‖ ^ 2 / n - 1) 2 (stdGaussian (Vector n)) :=
    (memLp_gaussian_normalized_norm_sq n).sub (memLp_const 1)
  have hA : MemLp (fun g : Vector n ↦ |‖g‖ ^ 2 / n - 1|) 2 (stdGaussian (Vector n)) := by
    simpa only [Real.norm_eq_abs] using hD.norm
  have hv := variance_nonneg (fun g : Vector n ↦ |‖g‖ ^ 2 / n - 1|) (stdGaussian (Vector n))
  rw [variance_eq_sub hA] at hv
  change 0 ≤ (∫ g : Vector n, |‖g‖ ^ 2 / n - 1| ^ 2 ∂stdGaussian (Vector n)) -
    (∫ g : Vector n, |‖g‖ ^ 2 / n - 1| ∂stdGaussian (Vector n)) ^ 2 at hv
  simp only [sq_abs, integral_gaussian_normalized_norm_sq_deviation_sq hn] at hv
  exact Real.le_sqrt_of_sq_le (by linarith)

end NLA.RowDeletion
