import NLA.RowDeletion.GaussianExponential
import Mathlib.Probability.Moments.MGFAnalytic

/-! # Scalar Gaussian moments from the existing exponential integral

Differentiating the Gaussian-square MGF twice supplies the fourth moment.
This avoids a new integration-by-parts argument or a separate chi-square law.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace NLA.RowDeletion

lemma gaussian_sq_mem_interior_integrableExpSet {t : ℝ} (ht : t < 1 / 2) :
    t ∈ interior (integrableExpSet (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1)) := by
  apply interior_mono (s := Set.Iio (1 / 2)) (fun s hs ↦ integrable_exp_gaussian_sq hs)
  simpa using ht

private lemma hasDerivAt_inv_sqrt_one_sub_two_mul {t : ℝ} (ht : t < 1 / 2) :
    HasDerivAt (fun s : ℝ ↦ (Real.sqrt (1 - 2 * s))⁻¹)
      ((Real.sqrt (1 - 2 * t))⁻¹ ^ 3) t := by
  have hp : 0 < 1 - 2 * t := by linarith
  have h := (((hasDerivAt_id t).const_mul 2).const_sub 1).sqrt hp.ne'
  convert! h.inv (Real.sqrt_pos.mpr hp).ne' using 1
  dsimp
  field_simp [(Real.sqrt_pos.mpr hp).ne']

lemma integral_gaussian_fourth : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  have hfirst {t : ℝ} (ht : t < 1 / 2) :
      (∫ x : ℝ, x ^ 2 * Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
        (Real.sqrt (1 - 2 * t))⁻¹ ^ 3 := by
    have he : mgf (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) =ᶠ[𝓝 t]
        (fun s : ℝ ↦ (Real.sqrt (1 - 2 * s))⁻¹) := by
      filter_upwards [eventually_lt_nhds ht] with s hs
      exact integral_exp_gaussian_sq hs
    exact (hasDerivAt_mgf (gaussian_sq_mem_interior_integrableExpSet ht)).unique
      ((hasDerivAt_inv_sqrt_one_sub_two_mul ht).congr_of_eventuallyEq he)
  have he : (fun t : ℝ ↦ ∫ x : ℝ, x ^ 2 * Real.exp (t * x ^ 2) ∂gaussianReal 0 1)
      =ᶠ[𝓝 0] (fun t : ℝ ↦ (Real.sqrt (1 - 2 * t))⁻¹ ^ 3) := by
    filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
    exact hfirst ht
  have hsecond := hasDerivAt_integral_pow_mul_exp_real
    (gaussian_sq_mem_interior_integrableExpSet (by norm_num : (0 : ℝ) < 1 / 2)) 1
  have hformula := (hasDerivAt_inv_sqrt_one_sub_two_mul
    (by norm_num : (0 : ℝ) < 1 / 2)).pow 3
  norm_num at hformula
  have hfourth : HasDerivAt
      (fun t : ℝ ↦ ∫ x : ℝ, x ^ 2 * Real.exp (t * x ^ 2) ∂gaussianReal 0 1)
      (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) 0 := by
    simpa [← pow_mul] using hsecond
  exact hfourth.unique (hformula.congr_of_eventuallyEq he)

lemma memLp_gaussian_sq : MemLp (fun x : ℝ ↦ x ^ 2) 2 (gaussianReal 0 1) :=
  memLp_of_mem_interior_integrableExpSet
    (gaussian_sq_mem_interior_integrableExpSet (by norm_num : (0 : ℝ) < 1 / 2)) 2

lemma integrable_gaussian_fourth : Integrable (fun x : ℝ ↦ x ^ 4) (gaussianReal 0 1) := by
  convert! memLp_gaussian_sq.integrable_sq using 1
  funext x
  ring

lemma variance_gaussian_sq : Var[fun x : ℝ ↦ x ^ 2; gaussianReal 0 1] = 2 := by
  rw [variance_eq_sub memLp_gaussian_sq]
  change (∫ x : ℝ, (x ^ 2) ^ 2 ∂gaussianReal 0 1) -
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) ^ 2 = 2
  simp only [← pow_mul]
  norm_num [integral_gaussian_fourth, integral_gaussian_sq]

end NLA.RowDeletion
