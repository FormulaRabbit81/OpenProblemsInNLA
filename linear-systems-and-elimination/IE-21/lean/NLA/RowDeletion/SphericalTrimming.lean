import NLA.RowDeletion.SphericalProjection
import NLA.RowDeletion.TrimmingTransport

/-! # Comparing spherical and Gaussian population trimming

The radius coupling and the shared 1-Lipschitz population-trimming estimate
control the difference by sqrt(2/n). This includes the two-point sphere in
dimension one and never assumes that spherical projections have continuous laws.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace NLA.RowDeletion

/-- Population trimming of a scaled squared unit-direction spherical projection
is within sqrt(2/n) of the standard Gaussian squared projection. -/
theorem abs_populationTrimmedMoment_spherical_sub_gaussian_le {n : ℕ}
    (hn : 0 < n) {b : Vector n} (hb : ‖b‖ = 1) {θ : ℝ} (hθ : θ ≤ 1) :
    |populationTrimmedMoment (sphericalLaw n) θ (fun u ↦ (n : ℝ) * (inner ℝ b u) ^ 2) -
      populationTrimmedMoment (gaussianReal 0 1) θ (fun x : ℝ ↦ x ^ 2)| ≤
        Real.sqrt (2 / n) := by
  have hs : populationTrimmedMoment (sphericalLaw n) θ
      (fun u ↦ (n : ℝ) * (inner ℝ b u) ^ 2) =
        populationTrimmedMoment (stdGaussian (Vector n)) θ
          (fun g ↦ (n : ℝ) * (inner ℝ b (sphereDirection g)) ^ 2) := by
    rw [← stdGaussian_map_sphereDirection hn,
      populationTrimmedMoment_map _ (measurable_sphereDirection n) (by fun_prop)]
    rfl
  have hg : populationTrimmedMoment (gaussianReal 0 1) θ (fun x : ℝ ↦ x ^ 2) =
      populationTrimmedMoment (stdGaussian (Vector n)) θ (fun g ↦ (inner ℝ b g) ^ 2) := by
    rw [← stdGaussian_map_inner_unit hb, populationTrimmedMoment_map _ (by fun_prop) (by fun_prop)]
    rfl
  rw [hs, hg]
  apply (abs_populationTrimmedMoment_sub_le
    (integrable_spherical_projection_sq_gaussian hn b) (integrable_gaussian_inner_sq b) hθ).trans
  simpa only [hb, one_pow, one_mul] using
    integral_abs_spherical_projection_sq_sub_gaussian_le hn b

/-- The spherical population constant is within sqrt(2/n) of the canonical
Gaussian trimmed second moment h_theta, uniformly over all unit directions. -/
theorem abs_populationTrimmedMoment_spherical_sub_gaussianTrimmedMoment_le {n : ℕ}
    (hn : 0 < n) {b : Vector n} (hb : ‖b‖ = 1) {θ a : ℝ}
    (hθ : θ ≤ 1) (ha : GaussianCutoff θ a) :
    |populationTrimmedMoment (sphericalLaw n) θ (fun u ↦ (n : ℝ) * (inner ℝ b u) ^ 2) -
      gaussianTrimmedMoment a| ≤ Real.sqrt (2 / n) := by
  rw [← populationTrimmedMoment_gaussian ha]
  exact abs_populationTrimmedMoment_spherical_sub_gaussian_le hn hb hθ

end NLA.RowDeletion
