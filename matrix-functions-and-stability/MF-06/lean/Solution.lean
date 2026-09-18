/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
Epperlein and Wirth retain attribution for the original question. Reused MF05
and MF07 mathematics retain Matthew J. Colbrook's credit and code authorship.
All 38 independent contracts are exported from the complete canonical proof.
-/
import NLA.MF06.CanonicalLower

set_option autoImplicit false
set_option leancert.trust "kernel"

#print axioms NLA.MF05.half_radius_certificate
#assert_trust kernel NLA.MF05.half_radius_certificate
#print axioms NLA.MF05.spectral_hausdorff_semantics
#assert_trust kernel NLA.MF05.spectral_hausdorff_semantics
#print axioms NLA.MF05.general_root_limit_semantics
#assert_trust kernel NLA.MF05.general_root_limit_semantics
#print axioms NLA.MF05.positive_scaling_semantics
#assert_trust kernel NLA.MF05.positive_scaling_semantics
#print axioms NLA.MF06.bounded_envelope_norm
#assert_trust kernel NLA.MF06.bounded_envelope_norm
#print axioms NLA.MF06.tail_seminorm_limit
#assert_trust kernel NLA.MF06.tail_seminorm_limit
#print axioms NLA.MF06.stable_gauge_max_recurrence
#assert_trust kernel NLA.MF06.stable_gauge_max_recurrence
#print axioms NLA.MF06.stable_kernel_exponential
#assert_trust kernel NLA.MF06.stable_kernel_exponential
#print axioms NLA.MF06.cone_numerical_bound
#assert_trust kernel NLA.MF06.cone_numerical_bound
#print axioms NLA.MF06.product_bounded_lower_lipschitz
#assert_trust kernel NLA.MF06.product_bounded_lower_lipschitz
#print axioms NLA.MF06.separated_sum_bound
#assert_trust kernel NLA.MF06.separated_sum_bound
#print axioms NLA.MF06.block_radius_formula
#assert_trust kernel NLA.MF06.block_radius_formula
#print axioms NLA.MF06.block_nonresonance_product_bounded
#assert_trust kernel NLA.MF06.block_nonresonance_product_bounded
#print axioms NLA.MF06.irreducible_radius_one_product_bounded
#assert_trust kernel NLA.MF06.irreducible_radius_one_product_bounded
#print axioms NLA.MF06.irreducible_flag
#assert_trust kernel NLA.MF06.irreducible_flag
#print axioms NLA.MF06.similarity_semantics
#assert_trust kernel NLA.MF06.similarity_semantics
#print axioms NLA.MF06.compound_dimensions
#assert_trust kernel NLA.MF06.compound_dimensions
#print axioms NLA.MF06.compound_coordinate_semantics
#assert_trust kernel NLA.MF06.compound_coordinate_semantics
#print axioms NLA.MF06.compound_algebra
#assert_trust kernel NLA.MF06.compound_algebra
#print axioms NLA.MF06.compound_norm_bound
#assert_trust kernel NLA.MF06.compound_norm_bound
#print axioms NLA.MF06.compound_local_lipschitz
#assert_trust kernel NLA.MF06.compound_local_lipschitz
#print axioms NLA.MF06.tensor_algebra
#assert_trust kernel NLA.MF06.tensor_algebra
#print axioms NLA.MF06.tensor_norm_comparison
#assert_trust kernel NLA.MF06.tensor_norm_comparison
#print axioms NLA.MF06.allocation_dimensions
#assert_trust kernel NLA.MF06.allocation_dimensions
#print axioms NLA.MF06.allocation_algebra
#assert_trust kernel NLA.MF06.allocation_algebra
#print axioms NLA.MF06.allocation_product_bounded
#assert_trust kernel NLA.MF06.allocation_product_bounded
#print axioms NLA.MF06.compound_allocation_radius
#assert_trust kernel NLA.MF06.compound_allocation_radius
#print axioms NLA.MF06.distinct_allocation_degrees
#assert_trust kernel NLA.MF06.distinct_allocation_degrees
#print axioms NLA.MF06.allocation_tensor_norm_bridge
#assert_trust kernel NLA.MF06.allocation_tensor_norm_bridge
#print axioms NLA.MF06.critical_allocation_nonresonance
#assert_trust kernel NLA.MF06.critical_allocation_nonresonance
#print axioms NLA.MF06.compound_nonresonance_product_bounded
#assert_trust kernel NLA.MF06.compound_nonresonance_product_bounded
#print axioms NLA.MF06.compound_family_semantics
#assert_trust kernel NLA.MF06.compound_family_semantics
#print axioms NLA.MF06.critical_compound_product_bounded
#assert_trust kernel NLA.MF06.critical_compound_product_bounded
#print axioms NLA.MF06.compound_hausdorff_bound
#assert_trust kernel NLA.MF06.compound_hausdorff_bound
#print axioms NLA.MF06.positive_hausdorff_scaling
#assert_trust kernel NLA.MF06.positive_hausdorff_scaling
#print axioms NLA.MF06.root_lower_bound
#assert_trust kernel NLA.MF06.root_lower_bound
#print axioms NLA.MF06.normalized_pointwise_lower_lipschitz
#assert_trust kernel NLA.MF06.normalized_pointwise_lower_lipschitz
#print axioms NLA.MF06.canonical_pointwise_lower_lipschitz
#assert_trust kernel NLA.MF06.canonical_pointwise_lower_lipschitz
