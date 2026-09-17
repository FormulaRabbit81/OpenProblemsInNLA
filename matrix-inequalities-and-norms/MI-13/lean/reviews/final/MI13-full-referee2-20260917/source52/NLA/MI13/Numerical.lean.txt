/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

The frozen positive-half certificate is to be consumed by Frobenius averaging.
No variable interval subdivision or numerical matrix computation is needed.
-/
import NLA.MI13.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI13
noncomputable section

theorem half_certificate : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) + 1 / 2 = 1 := by
  constructor
  · interval_decide (trust := kernel)
  · norm_num

#print axioms half_certificate
#assert_trust kernel half_certificate

end
end NLA.MI13
