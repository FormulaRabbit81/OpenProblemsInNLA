/-
Current checked checkpoint. The source's quantitative planted-law, Haar-overlap
and likelihood-comparison estimates are deliberately absent rather than
represented by axioms or unproved declarations.
-/
import NLA.FR05.Obstruction
import NLA.FR05.RankTwoSeed
import NLA.FR05.MainReduction

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

/-- Existential form of the all-dimension exact ambiguity checkpoint. -/
theorem explicit_noninjective_frame_proved (d : ℕ) (hd : 2 ≤ d) :
    ∃ A : Frame (4 * d - 5) d, ¬ PhaseRetrievalInjective A := by
  refine ⟨flatFrame (4 * d - 5) d, ?_⟩
  exact flatFrame_not_phaseRetrievalInjective d hd

end NLA.FR05
