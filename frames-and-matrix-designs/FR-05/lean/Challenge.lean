import NLA.FR05.Probability

/-!
Unreviewed development boundary for an incomplete partial checkpoint.
The placeholders below are intentionally isolated: `Solution` and all its
dependencies do not import this module. It is not a formalisation of the
FR-05 probability theorem.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace NLA.FR05

theorem explicit_noninjective_frame (d : ℕ) (hd : 2 ≤ d) :
    ∃ A : Frame (4 * d - 5) d, ¬ PhaseRetrievalInjective A := by
  sorry

/-- The exact quantitative target from Li's Theorem 1.4. This declaration is
currently a challenge-only specification, not a checked result. -/
theorem phaseRetrieval_injective_probability_le_inv :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      phaseRetrievalProbability d ≤ C / d := by
  sorry

/-- The exact algebraic reduction at the end of Proposition 3.2. The
source-specific likelihoods and their second-moment estimates remain a
challenge-only analytic obligation. -/
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
  sorry

end NLA.FR05
