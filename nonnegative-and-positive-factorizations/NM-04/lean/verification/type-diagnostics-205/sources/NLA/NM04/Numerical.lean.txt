/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance; original mathematical attribution retained.

The two exact ground bounds used to select a positive, strictly smaller
coercivity coefficient. Their eventual consumer is the constrained potential
minimization proof. No numerical approximation of a matrix or logarithm is used.
-/
import NLA.NM04.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04

theorem coercivity_half_certificate :
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by
  constructor <;> interval_decide (trust := kernel)

#print axioms coercivity_half_certificate
#assert_trust kernel coercivity_half_certificate

end NLA.NM04
