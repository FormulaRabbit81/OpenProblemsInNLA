/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

The exact radius is 1/16. Only closed rational inequalities need LeanCert;
the downstream box bounds consume this certificate without subdivisions.
-/
import NLA.SP15.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section

theorem box_scalar_certificate :
    0 < boxRadius ∧ 0 < 1 - boxRadius ∧ 0 < 1 - 2 * boxRadius ∧
    3 * (1 + boxRadius) < 4 - boxRadius ∧
    (4 - boxRadius) - 3 * (1 + boxRadius) = (3 / 4 : ℝ) := by
  unfold boxRadius
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · interval_decide (trust := kernel)
  · interval_decide (trust := kernel)
  · interval_decide (trust := kernel)
  · interval_decide (trust := kernel)
  · norm_num

#print axioms box_scalar_certificate
#assert_trust kernel box_scalar_certificate

end
end NLA.SP15
