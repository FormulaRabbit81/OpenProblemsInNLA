import NLA.RowDeletion.Definitions
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Tactic

/-!
# Real Gaussian projection interface

The projection-law proof follows the direct Mathlib transport used in
FR-05/Gaussian/GaussianProjection.lean, with the standard REAL Gaussian
variance convention. No FR-05 theorem or complex probability law is imported.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace NLA.RowDeletion

theorem stdGaussian_map_inner {n : ℕ} (b : Vector n) :
    (stdGaussian (Vector n)).map (fun g ↦ inner ℝ b g) =
      gaussianReal 0 (‖b‖ ^ 2).toNNReal := by
  change (stdGaussian (Vector n)).map (innerSL ℝ b) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm]

theorem measurePreserving_gaussian_inner {n : ℕ} (b : Vector n) :
    MeasurePreserving (fun g ↦ inner ℝ b g) (stdGaussian (Vector n))
      (gaussianReal 0 (‖b‖ ^ 2).toNNReal) :=
  ⟨by fun_prop, stdGaussian_map_inner b⟩

theorem stdGaussian_map_inner_unit {n : ℕ} {b : Vector n} (hb : ‖b‖ = 1) :
    (stdGaussian (Vector n)).map (fun g ↦ inner ℝ b g) = gaussianReal 0 1 := by
  simpa [hb] using stdGaussian_map_inner b

theorem integral_gaussian_inner {n : ℕ} (b : Vector n) :
    (∫ g, inner ℝ b g ∂stdGaussian (Vector n)) = 0 :=
  integral_strongDual_stdGaussian (innerSL ℝ b)

theorem variance_gaussian_inner {n : ℕ} (b : Vector n) :
    Var[fun g ↦ inner ℝ b g; stdGaussian (Vector n)] = ‖b‖ ^ 2 := by
  simpa using variance_dual_stdGaussian (innerSL ℝ b)

end NLA.RowDeletion
