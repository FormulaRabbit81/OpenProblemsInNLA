import NLA.FR05.Probability

/-!
Unreviewed development boundary for the completed deterministic checkpoint.
The placeholder below is intentionally isolated: `Solution` and all its
dependencies do not import this module. It is not a formalisation of the
FR-05 probability theorem.
-/

set_option autoImplicit false
noncomputable section

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

end NLA.FR05
