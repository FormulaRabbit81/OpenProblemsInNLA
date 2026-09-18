/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance; prior mathematical attribution retained.

The sole numerical certificate is the exact rational positive half. Its named
result supplies the positive scalar in the actual descent-step bounds.
-/
import NLA.IE02.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02

theorem half_certificate : (0 : ℝ) < 1 / 2 := by
  interval_decide (trust := kernel)

#print axioms half_certificate
#assert_trust kernel half_certificate

end NLA.IE02
