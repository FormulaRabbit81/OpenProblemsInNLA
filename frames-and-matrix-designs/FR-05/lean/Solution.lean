/-
Kernel-checked FR-05 checkpoint. The unconditional probabilistic theorem
remains outside this development checkpoint.
-/
import NLA.FR05.Proof

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ComplexConjugate
noncomputable section

namespace NLA.FR05

theorem explicit_noninjective_frame (d : ℕ) (hd : 2 ≤ d) :
    ∃ A : Frame (4 * d - 5) d, ¬ PhaseRetrievalInjective A := by
  exact explicit_noninjective_frame_proved d hd

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
#print axioms likelihood_l2_bound_of_second_moment_estimates
#print axioms phaseRetrieval_injective_probability_le_inv_of_source_comparison

end NLA.FR05
