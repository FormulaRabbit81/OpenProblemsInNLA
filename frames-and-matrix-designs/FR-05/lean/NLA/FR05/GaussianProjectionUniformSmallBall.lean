/-
Variance-uniform small-ball bound for an actual complex-Gaussian projection.

This transfers the scalar estimate from `NonTailConditionalSmallBall` through
the exact pushforward identity for `standardComplexGaussianTail`; no positive
lower bound on the projection variance is required.
-/
import NLA.FR05.NonTailConditionalSmallBall
import NLA.FR05.GaussianProjection
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- Away from the deterministic centre, the small-ball probability for the
real part of an actual standard complex-Gaussian projection is uniformly
bounded over all directions, including the zero direction. -/
theorem standardComplexGaussianTail_real_dotProduct_abs_add_smallBall_uniform
    {n : ℕ} (z : Signal n) (m u t : ℝ)
    (ht : 0 < t) (hcentre : t ≤ |m|) (hscale : 2 * u ≤ t) :
    standardComplexGaussianTail n
        {w : Signal n | |m + (star w ⬝ᵥ z).re| ≤ u} ≤
      ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  let f : Signal n → ℝ := fun w ↦ (star w ⬝ᵥ z).re
  let s : Set ℝ := {x : ℝ | |m + x| ≤ u}
  have hs : MeasurableSet s := by
    dsimp [s]
    change MeasurableSet ((fun x : ℝ ↦ |m + x|) ⁻¹' Iic u)
    apply MeasurableSet.preimage measurableSet_Iic
    fun_prop
  have hevent :
      {w : Signal n | |m + (star w ⬝ᵥ z).re| ≤ u} = f ⁻¹' s := by
    ext w
    rfl
  calc
    standardComplexGaussianTail n
        {w : Signal n | |m + (star w ⬝ᵥ z).re| ≤ u} =
        standardComplexGaussianTail n (f ⁻¹' s) := by rw [hevent]
    _ = (standardComplexGaussianTail n).map f s := by
      rw [Measure.map_apply (measurable_real_star_dotProduct z) hs]
    _ = gaussianReal 0 (signalEnergy z / 2).toNNReal s := by
      rw [show f = (fun w : Signal n ↦ (star w ⬝ᵥ z).re) by rfl,
        standardComplexGaussianTail_map_real_dotProduct]
    _ ≤ ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) :=
      gaussianReal_abs_add_smallBall_uniform m u t ht hcentre hscale

end NLA.FR05
