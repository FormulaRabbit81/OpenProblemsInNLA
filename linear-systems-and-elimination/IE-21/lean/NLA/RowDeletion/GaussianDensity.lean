import NLA.RowDeletion.Gaussian
import NLA.RowDeletion.RadialMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # The standard real Gaussian as a radial density

This follows from the existing independent-coordinate definition, not from a
new definition of the Gaussian law. The normalizing factor is left as a power
of the one-dimensional density constant.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace NLA.RowDeletion

def gaussianRadialDensity (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ n * Real.exp (-r ^ 2 / 2))

lemma measurable_gaussianRadialDensity (n : ℕ) : Measurable (gaussianRadialDensity n) := by
  unfold gaussianRadialDensity
  fun_prop

lemma pi_gaussian_eq_withDensity (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (fun _ ↦ (integrable_gaussianPDFReal 0 1).restrict))
    (ae_of_all _ (fun x ↦ Finset.prod_nonneg (fun i _ ↦ gaussianPDFReal_nonneg 0 1 (x i)))),
    integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ integral_nonneg (fun x ↦ gaussianPDFReal_nonneg 0 1 x))]
  exact Finset.prod_congr rfl fun i _ ↦ (gaussianReal_apply_eq_integral 0 one_ne_zero (s i)).symm

lemma prod_gaussianPDFReal_eq_radial (n : ℕ) (x : Fin n → ℝ) :
    ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i)) =
      gaussianRadialDensity n ‖WithLp.toLp 2 x‖ := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, ← Finset.sum_div, Finset.sum_neg_distrib,
    gaussianRadialDensity, EuclideanSpace.real_norm_sq_eq]

theorem stdGaussian_eq_radial_density (n : ℕ) :
    stdGaussian (Vector n) =
      (volume : Measure (Vector n)).withDensity (fun x ↦ gaussianRadialDensity n ‖x‖) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussian_eq_withDensity]
  simp_rw [prod_gaussianPDFReal_eq_radial]
  change (volume.withDensity ((fun x : Vector n ↦ gaussianRadialDensity n ‖x‖) ∘
    WithLp.toLp 2)).map (WithLp.toLp 2) = _
  rw [map_withDensity_comp _ (by fun_prop) (by
    exact (measurable_gaussianRadialDensity n).comp measurable_norm),
    (PiLp.volume_preserving_toLp (Fin n)).map_eq]

end NLA.RowDeletion
