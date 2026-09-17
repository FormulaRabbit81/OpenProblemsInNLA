/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Partial resolvent-prefix check commands only. This is not a Solution or
evidence that kernel, numerical or Comparator checks have executed.
-/
import NLA.SF01.SpectralBridgeChecks
import NLA.SF01.ResolventDomination

set_option autoImplicit false
set_option leancert.trust "kernel"

#print axioms NLA.SF01.shifted_positiveWeight
#assert_trust kernel NLA.SF01.shifted_positiveWeight
#print axioms NLA.SF01.shift_comparison
#assert_trust kernel NLA.SF01.shift_comparison
#print axioms NLA.SF01.H_shift_structure
#assert_trust kernel NLA.SF01.H_shift_structure
#print axioms NLA.SF01.comparison_abs_mulVec_general
#assert_trust kernel NLA.SF01.comparison_abs_mulVec_general
#print axioms NLA.SF01.comparison_abs_mulVec
#assert_trust kernel NLA.SF01.comparison_abs_mulVec
#print axioms NLA.SF01.inverse_mulVec_column
#assert_trust kernel NLA.SF01.inverse_mulVec_column
#print axioms NLA.SF01.resolvent_domination
#assert_trust kernel NLA.SF01.resolvent_domination
