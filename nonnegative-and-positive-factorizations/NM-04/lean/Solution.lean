/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Matthew J. Colbrook retains the mathematical
solution of Rowland and Wu's coefficient question. All 35 independent contracts
are exported from the actual complete canonical proof closure below.
-/
import NLA.NM04.Canonical
import NLA.NM04.TransitionEntries

set_option autoImplicit false
set_option leancert.trust "kernel"

#print axioms NLA.NM04.coercivity_half_certificate
#assert_trust kernel NLA.NM04.coercivity_half_certificate
#print axioms NLA.NM04.row_partition_positive
#assert_trust kernel NLA.NM04.row_partition_positive
#print axioms NLA.NM04.potential_continuous
#assert_trust kernel NLA.NM04.potential_continuous
#print axioms NLA.NM04.potential_line_derivative
#assert_trust kernel NLA.NM04.potential_line_derivative
#print axioms NLA.NM04.zero_mean_coercivity
#assert_trust kernel NLA.NM04.zero_mean_coercivity
#print axioms NLA.NM04.potential_attains_minimum
#assert_trust kernel NLA.NM04.potential_attains_minimum
#print axioms NLA.NM04.potential_minimum_has_margins
#assert_trust kernel NLA.NM04.potential_minimum_has_margins
#print axioms NLA.NM04.positive_balanced_scaling_exists
#assert_trust kernel NLA.NM04.positive_balanced_scaling_exists
#print axioms NLA.NM04.positive_balanced_scaling_unique
#assert_trust kernel NLA.NM04.positive_balanced_scaling_unique
#print axioms NLA.NM04.sinkhorn_semantics
#assert_trust kernel NLA.NM04.sinkhorn_semantics
#print axioms NLA.NM04.position_sorted_semantics
#assert_trust kernel NLA.NM04.position_sorted_semantics
#print axioms NLA.NM04.empty_minor_values
#assert_trust kernel NLA.NM04.empty_minor_values
#print axioms NLA.NM04.H_diagonal
#assert_trust kernel NLA.NM04.H_diagonal
#print axioms NLA.NM04.H_raising
#assert_trust kernel NLA.NM04.H_raising
#print axioms NLA.NM04.H_lowering
#assert_trust kernel NLA.NM04.H_lowering
#print axioms NLA.NM04.H_column_exchange
#assert_trust kernel NLA.NM04.H_column_exchange
#print axioms NLA.NM04.H_row_exchange
#assert_trust kernel NLA.NM04.H_row_exchange
#print axioms NLA.NM04.H_other
#assert_trust kernel NLA.NM04.H_other
#print axioms NLA.NM04.weighted_principal_minor_expansion
#assert_trust kernel NLA.NM04.weighted_principal_minor_expansion
#print axioms NLA.NM04.cofactor_signed_minor_formula
#assert_trust kernel NLA.NM04.cofactor_signed_minor_formula
#print axioms NLA.NM04.universal_rank_one_update
#assert_trust kernel NLA.NM04.universal_rank_one_update
#print axioms NLA.NM04.universal_bordered_determinant
#assert_trust kernel NLA.NM04.universal_bordered_determinant
#print axioms NLA.NM04.minor_lowering_identity
#assert_trust kernel NLA.NM04.minor_lowering_identity
#print axioms NLA.NM04.minor_column_exchange_identity
#assert_trust kernel NLA.NM04.minor_column_exchange_identity
#print axioms NLA.NM04.minor_row_exchange_identity
#assert_trust kernel NLA.NM04.minor_row_exchange_identity
#print axioms NLA.NM04.minor_raising_identity
#assert_trust kernel NLA.NM04.minor_raising_identity
#print axioms NLA.NM04.schur_margin_identities
#assert_trust kernel NLA.NM04.schur_margin_identities
#print axioms NLA.NM04.schur_bordered_minor
#assert_trust kernel NLA.NM04.schur_bordered_minor
#print axioms NLA.NM04.balanced_minor_relation
#assert_trust kernel NLA.NM04.balanced_minor_relation
#print axioms NLA.NM04.weighted_transition_action
#assert_trust kernel NLA.NM04.weighted_transition_action
#print axioms NLA.NM04.balanced_null_vector
#assert_trust kernel NLA.NM04.balanced_null_vector
#print axioms NLA.NM04.diagonal_minor_covariance
#assert_trust kernel NLA.NM04.diagonal_minor_covariance
#print axioms NLA.NM04.diagonal_pencil_covariance
#assert_trust kernel NLA.NM04.diagonal_pencil_covariance
#print axioms NLA.NM04.sinkhorn_pencil_singular
#assert_trust kernel NLA.NM04.sinkhorn_pencil_singular
#print axioms NLA.NM04.rowland_wu_identity
#assert_trust kernel NLA.NM04.rowland_wu_identity
