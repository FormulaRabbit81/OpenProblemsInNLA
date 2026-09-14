/-
Kernel-checked FR-05 checkpoint. The unconditional probabilistic theorem
remains outside this development checkpoint.
-/
import NLA.FR05.Proof

set_option autoImplicit false
open scoped BigOperators ComplexConjugate
noncomputable section

namespace NLA.FR05

theorem explicit_noninjective_frame (d : ℕ) (hd : 2 ≤ d) :
    ∃ A : Frame (4 * d - 5) d, ¬ PhaseRetrievalInjective A := by
  exact explicit_noninjective_frame_proved d hd

#print axioms explicit_noninjective_frame
#print axioms phaseRetrieval_injective_probability_le_inv_of_source_comparison

end NLA.FR05
