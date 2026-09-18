/-
Kernel-checked FR-05 checkpoint. The unconditional probabilistic theorem
remains outside this development checkpoint.
-/
import NLA.FR05.Proof

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
noncomputable section

namespace NLA.FR05

theorem explicit_noninjective_frame (d : ℕ) (hd : 2 ≤ d) :
    ∃ A : Frame (4 * d - 5) d, ¬ PhaseRetrievalInjective A := by
  exact explicit_noninjective_frame_proved d hd

/-- The exact iid planted-frame law used in the source's Proposition 3.1
factors through the checked deterministic planted-row construction. -/
theorem source_planted_frame_law_representation {M : ℕ} (hM : 1 ≤ M) :
    sourcePlantedFrameLawAt M =
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M)
        (sourceRowCount M) (sourceTailDimension M)).map
        (fun p => plantedFrame (sourceRowsFromCoordinates p)) := by
  exact sourcePlantedFrameLawAt_eq_viaPlantedRows hM

/-- The radial coordinate of the source's planted law has the explicit
exponential tail used in its norm event. -/
theorem source_planted_radial_tail {M : ℕ} (hM : 1 ≤ M) :
    sourceRadialLaw sourceEta (sourceDelta M) (Set.Ici (8 * (M : ℝ))) ≤
      (25 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(4 * (M : ℝ)))) := by
  exact sourceRadialLaw_sourceM_apply_Ici_le hM

theorem likelihood_l2_bound_of_second_moment_estimates
    {Ω : ℕ → Type*} [∀ M, MeasurableSpace (Ω M)]
    (μ : ∀ M, Measure (Ω M)) (Lg Lr : ∀ M, Ω M → ℝ)
    (D : ℕ) (C : ℝ)
    (hcomparisons : ∀ M : ℕ, D ≤ M →
      Integrable (fun ω ↦ Lg M ω * Lg M ω) (μ M) ∧
      Integrable (fun ω ↦ Lr M ω * Lr M ω) (μ M) ∧
      Integrable (fun ω ↦ Lg M ω * Lr M ω) (μ M) ∧
      |(∫ ω, Lg M ω * Lg M ω ∂μ M) -
        (∫ ω, Lr M ω * Lr M ω ∂μ M)| ≤ C / M ∧
      |(∫ ω, Lg M ω * Lr M ω ∂μ M) -
        (∫ ω, Lr M ω * Lr M ω ∂μ M)| ≤ C / M) :
    ∀ M : ℕ, D ≤ M →
      (∫ ω, (Lg M ω - Lr M ω) ^ 2 ∂μ M) ≤ 3 * C / M := by
  exact eventual_likelihood_l2_le_of_second_moment_comparisons_proved
    μ Lg Lr D C hcomparisons

#print axioms explicit_noninjective_frame
#print axioms source_planted_frame_law_representation
#print axioms source_planted_radial_tail
#print axioms likelihood_l2_bound_of_second_moment_estimates
#print axioms phaseRetrieval_injective_probability_le_inv_of_source_comparison

end NLA.FR05
