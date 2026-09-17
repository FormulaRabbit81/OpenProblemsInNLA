/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Proposed complete 24-contract check entrypoint. No successful execution is
claimed by this source. This imports implementations and never Challenge.
-/
import NLA.SF01.NewtonConclusion

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SF01

#print axioms complex_spectral_radius_semantics
#assert_trust kernel complex_spectral_radius_semantics
#print axioms spectral_radius_strict_bound
#assert_trust kernel spectral_radius_strict_bound
#print axioms spectral_homotopy_isUnit
#assert_trust kernel spectral_homotopy_isUnit
#print axioms spectralM_positive_weight
#assert_trust kernel spectralM_positive_weight
#print axioms weighted_Z_spectralM
#assert_trust kernel weighted_Z_spectralM
#print axioms H_positive_weight
#assert_trust kernel H_positive_weight
#print axioms shift_comparison
#assert_trust kernel shift_comparison
#print axioms H_shift_structure
#assert_trust kernel H_shift_structure
#print axioms comparison_abs_mulVec
#assert_trust kernel comparison_abs_mulVec
#print axioms resolvent_domination
#assert_trust kernel resolvent_domination
#print axioms half_positive_certificate
#assert_trust kernel half_positive_certificate
#print axioms ridge_comparison_preserver
#assert_trust kernel ridge_comparison_preserver
#print axioms ridge_commutes
#assert_trust kernel ridge_commutes
#print axioms pole_positive_definite
#assert_trust kernel pole_positive_definite
#print axioms pole_diagonalization_exists
#assert_trust kernel pole_diagonalization_exists
#print axioms pole_residue_normalization
#assert_trust kernel pole_residue_normalization
#print axioms reciprocal_weights_nonnegative
#assert_trust kernel reciprocal_weights_nonnegative
#print axioms reciprocal_blocks_isUnit
#assert_trust kernel reciprocal_blocks_isUnit
#print axioms matrix_reciprocal_identity
#assert_trust kernel matrix_reciprocal_identity
#print axioms newton_data_step
#assert_trust kernel newton_data_step
#print axioms initial_data_valid
#assert_trust kernel initial_data_valid
#print axioms newton_first
#assert_trust kernel newton_first
#print axioms iterate_ridge_representation
#assert_trust kernel iterate_ridge_representation
#print axioms canonical_newton_preservation
#assert_trust kernel canonical_newton_preservation

end NLA.SF01
