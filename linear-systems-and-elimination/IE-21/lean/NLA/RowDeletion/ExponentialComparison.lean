import NLA.RowDeletion.PopulationTrimming
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! # Independent mean-one multipliers

Jensen's inequality compares exponential moments before and after multiplication
by an independent mean-one factor. It applies to both signs of the exponential
parameter, avoiding a separate computation of spherical even moments.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NLA.RowDeletion

theorem exp_le_integral_exp_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : Ω → ℝ} (hD : Integrable D μ) (hmean : ∫ ω, D ω ∂μ = 1)
    (c : ℝ) (he : Integrable (fun ω ↦ Real.exp (c * D ω)) μ) :
    Real.exp c ≤ ∫ ω, Real.exp (c * D ω) ∂μ := by
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (ae_of_all μ fun _ ↦ Set.mem_univ _) (hD.const_mul c) he
  simpa only [integral_const_mul, hmean, mul_one] using hj

/-- A product-measure formulation makes the independence assumption explicit. -/
theorem integral_exp_le_integral_exp_independent_mul
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Y : Ω → ℝ} {D : Ξ → ℝ} (hD : Integrable D ν) (hmean : ∫ ω, D ω ∂ν = 1)
    (c : ℝ) (hY : Integrable (fun ω ↦ Real.exp (c * Y ω)) μ)
    (hprod : Integrable (fun p : Ω × Ξ ↦ Real.exp (c * Y p.1 * D p.2)) (μ.prod ν)) :
    (∫ ω, Real.exp (c * Y ω) ∂μ) ≤
      ∫ p : Ω × Ξ, Real.exp (c * Y p.1 * D p.2) ∂μ.prod ν := by
  rw [integral_prod _ hprod]
  apply integral_mono_ae hY hprod.integral_prod_left
  filter_upwards [hprod.prod_right_ae] with ω hω
  exact exp_le_integral_exp_mul hD hmean (c * Y ω) hω

end NLA.RowDeletion
