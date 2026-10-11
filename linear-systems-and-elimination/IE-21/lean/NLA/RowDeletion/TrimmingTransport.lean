import NLA.RowDeletion.PopulationTrimming

/-! # Population trimming depends only on the law

Transporting the hinge integrals through a measurable map transports their
supremum. These identities require no quantile or continuity assumption.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NLA.RowDeletion

lemma populationThreshold_map {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) {f : Ω → Ξ} (hf : Measurable f) {Y : Ξ → ℝ} (hY : Measurable Y)
    (θ t : ℝ) :
    populationThreshold (μ.map f) θ Y t = populationThreshold μ θ (Y ∘ f) t := by
  unfold populationThreshold
  rw [integral_map hf.aemeasurable (by unfold hinge; fun_prop)]
  rfl

/-- The same population trimming functional may be evaluated on any realization of its law. -/
theorem populationTrimmedMoment_map {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) {f : Ω → Ξ} (hf : Measurable f) {Y : Ξ → ℝ} (hY : Measurable Y)
    (θ : ℝ) :
    populationTrimmedMoment (μ.map f) θ Y = populationTrimmedMoment μ θ (Y ∘ f) := by
  have h : populationThreshold (μ.map f) θ Y = populationThreshold μ θ (Y ∘ f) := by
    funext t
    exact populationThreshold_map μ hf hY θ t
  unfold populationTrimmedMoment
  rw [h]

end NLA.RowDeletion
