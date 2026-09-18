/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical proof:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge. Exact published MF07 code authorship is preserved.

Aggregate of all fourteen frozen MF05 obligations. Challenge is not imported.
The prints and kernel trust checks expose the transitive axiom dependencies.
-/
import NLA.MF05.Final

set_option autoImplicit false
set_option leancert.trust "kernel"

#print axioms NLA.MF05.half_radius_certificate
#assert_trust kernel NLA.MF05.half_radius_certificate
#print axioms NLA.MF05.spectral_hausdorff_semantics
#assert_trust kernel NLA.MF05.spectral_hausdorff_semantics
#print axioms NLA.MF05.general_exponential_envelope
#assert_trust kernel NLA.MF05.general_exponential_envelope
#print axioms NLA.MF05.general_root_limit_semantics
#assert_trust kernel NLA.MF05.general_root_limit_semantics
#print axioms NLA.MF05.positive_scaling_semantics
#assert_trust kernel NLA.MF05.positive_scaling_semantics
#print axioms NLA.MF05.exponential_bound_controls_radius
#assert_trust kernel NLA.MF05.exponential_bound_controls_radius
#print axioms NLA.MF05.scalar_identity_adjoin_radius
#assert_trust kernel NLA.MF05.scalar_identity_adjoin_radius
#print axioms NLA.MF05.general_quantitative_comparison
#assert_trust kernel NLA.MF05.general_quantitative_comparison
#print axioms NLA.MF05.controlled_comparison_norm
#assert_trust kernel NLA.MF05.controlled_comparison_norm
#print axioms NLA.MF05.hausdorff_radius_transfer
#assert_trust kernel NLA.MF05.hausdorff_radius_transfer
#print axioms NLA.MF05.holder_scale_identity
#assert_trust kernel NLA.MF05.holder_scale_identity
#print axioms NLA.MF05.uniform_holder_estimate
#assert_trust kernel NLA.MF05.uniform_holder_estimate
#print axioms NLA.MF05.local_common_norm_ball
#assert_trust kernel NLA.MF05.local_common_norm_ball
#print axioms NLA.MF05.canonical_local_holder
#assert_trust kernel NLA.MF05.canonical_local_holder
