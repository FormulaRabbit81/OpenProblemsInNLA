/-
The completely formal, source-independent assembly of the quantitative
theorem. The analytic core of Li's manuscript is represented here by one
explicit eventual inequality, rather than by an axiom or an unproved export.
-/
import NLA.FR05.Assembly
import NLA.FR05.Probability

set_option autoImplicit false

namespace NLA.FR05

/-- An eventual instance of the source's final comparison is sufficient for
the advertised inverse bound. The hypotheses are the exact analytic
interface left to the planted-law and likelihood-comparison developments. -/
theorem phaseRetrieval_injective_probability_le_inv_of_source_comparison
    (D : ℕ) (a b : ℝ) (hD : 1 ≤ D) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (comparison : ∀ d : ℕ, D ≤ d →
      phaseRetrievalProbability d ≤ a / (d : ℝ) ^ 2 +
        Real.sqrt (b * phaseRetrievalProbability d / d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      phaseRetrievalProbability d ≤ C / d := by
  apply global_inverse_bound_of_eventual D phaseRetrievalProbability a b
  · exact phaseRetrievalProbability_le_one
  · intro d hd
    exact inverse_bound_of_source_comparison d (hD.trans hd)
      (phaseRetrievalProbability d) a b
      (phaseRetrievalProbability_nonneg d) ha hb (comparison d hd)

end NLA.FR05
