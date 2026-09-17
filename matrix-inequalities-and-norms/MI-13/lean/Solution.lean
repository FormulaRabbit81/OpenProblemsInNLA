/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Nobori's original question, Audenaert's
refined commutator theorem, and the repository reduction retain their attribution.

Complete 36-contract check entrypoint. Execution status is recorded separately.
This imports implementations only and never the independent Challenge.
-/
import NLA.MI13.Complete
import NLA.MI13.Sharpness

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI13

#print axioms frobenius_semantics
#assert_trust kernel frobenius_semantics
#print axioms frobenius_linear_bounds
#assert_trust kernel frobenius_linear_bounds
#print axioms operator_norm_semantics
#assert_trust kernel operator_norm_semantics
#print axioms singular_values_semantics
#assert_trust kernel singular_values_semantics
#print axioms singular_values_gram
#assert_trust kernel singular_values_gram
#print axioms ordered_gram_basis
#assert_trust kernel ordered_gram_basis
#print axioms positive_image_orthonormal
#assert_trust kernel positive_image_orthonormal
#print axioms zero_singular_image
#assert_trust kernel zero_singular_image
#print axioms positive_image_extension
#assert_trust kernel positive_image_extension
#print axioms full_singular_vector_bases
#assert_trust kernel full_singular_vector_bases
#print axioms full_svd
#assert_trust kernel full_svd
#print axioms unitary_norm_invariance
#assert_trust kernel unitary_norm_invariance
#print axioms unitary_singular_invariance
#assert_trust kernel unitary_singular_invariance
#print axioms hilbert_schmidt_semantics
#assert_trust kernel hilbert_schmidt_semantics
#print axioms commutator_adjoint
#assert_trust kernel commutator_adjoint
#print axioms commutator_conjugate_symmetry
#assert_trust kernel commutator_conjugate_symmetry
#print axioms commutator_spectral_maximum
#assert_trust kernel commutator_spectral_maximum
#print axioms positive_eigenvector_pair
#assert_trust kernel positive_eigenvector_pair
#print axioms eigenspace_functional_kernel
#assert_trust kernel eigenspace_functional_kernel
#print axioms two_coordinate_bound
#assert_trust kernel two_coordinate_bound
#print axioms off_corner_coefficient_bound
#assert_trust kernel off_corner_coefficient_bound
#print axioms svd_corner_functional
#assert_trust kernel svd_corner_functional
#print axioms cancelled_svd_bound
#assert_trust kernel cancelled_svd_bound
#print axioms refined_commutator_bound
#assert_trust kernel refined_commutator_bound
#print axioms half_certificate
#assert_trust kernel half_certificate
#print axioms unit_circle_lift
#assert_trust kernel unit_circle_lift
#print axioms two_unitary_average
#assert_trust kernel two_unitary_average
#print axioms frobenius_average_bound
#assert_trust kernel frobenius_average_bound
#print axioms unitary_middle_bound
#assert_trust kernel unitary_middle_bound
#print axioms contraction_middle_bound
#assert_trust kernel contraction_middle_bound
#print axioms square_middle_bound
#assert_trust kernel square_middle_bound
#print axioms padding_product
#assert_trust kernel padding_product
#print axioms padding_norms
#assert_trust kernel padding_norms
#print axioms padding_singular_values
#assert_trust kernel padding_singular_values
#print axioms canonical_rectangular_bound
#assert_trust kernel canonical_rectangular_bound
#print axioms sharpness_example
#assert_trust kernel sharpness_example

end NLA.MI13
