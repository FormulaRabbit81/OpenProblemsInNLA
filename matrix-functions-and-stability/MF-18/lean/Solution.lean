/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original complete complex MF-18 proof:
George Stepaniants. Guo, Kuo, and Lin retain attribution for the problem and
prior results. The separate real auxiliary theorem retains its authorship and
is not substituted for the canonical complex target.

These commands request axiom and kernel-trust checks for every frozen export.
Their presence is not evidence that the checks have been executed.
-/
import NLA.MF18.CanonicalRank
import NLA.MF18.StabilitySemantics

set_option autoImplicit false
set_option leancert.trust "kernel"

#print axioms NLA.MF18.certified_half
#assert_trust kernel NLA.MF18.certified_half
#print axioms NLA.MF18.stability_semantics
#assert_trust kernel NLA.MF18.stability_semantics
#print axioms NLA.MF18.pencil_evaluation
#assert_trust kernel NLA.MF18.pencil_evaluation
#print axioms NLA.MF18.pencil_degree_bound
#assert_trust kernel NLA.MF18.pencil_degree_bound
#print axioms NLA.MF18.positive_average_and_sign
#assert_trust kernel NLA.MF18.positive_average_and_sign
#print axioms NLA.MF18.homotopy_boundary_nonvanishing
#assert_trust kernel NLA.MF18.homotopy_boundary_nonvanishing
#print axioms NLA.MF18.cayley_degree_and_count
#assert_trust kernel NLA.MF18.cayley_degree_and_count
#print axioms NLA.MF18.cayley_boundary_transfer
#assert_trust kernel NLA.MF18.cayley_boundary_transfer
#print axioms NLA.MF18.monic_half_plane_count_homotopy
#assert_trust kernel NLA.MF18.monic_half_plane_count_homotopy
#print axioms NLA.MF18.bounded_degree_disk_count_homotopy
#assert_trust kernel NLA.MF18.bounded_degree_disk_count_homotopy
#print axioms NLA.MF18.regularized_root_count
#assert_trust kernel NLA.MF18.regularized_root_count
#print axioms NLA.MF18.solution_factorization
#assert_trust kernel NLA.MF18.solution_factorization
#print axioms NLA.MF18.complementary_stability
#assert_trust kernel NLA.MF18.complementary_stability
#print axioms NLA.MF18.closed_disk_stability_limit
#assert_trust kernel NLA.MF18.closed_disk_stability_limit
#print axioms NLA.MF18.limiting_equation_and_spectra
#assert_trust kernel NLA.MF18.limiting_equation_and_spectra
#print axioms NLA.MF18.reciprocal_count_identity
#assert_trust kernel NLA.MF18.reciprocal_count_identity
#print axioms NLA.MF18.selected_spectrum_count
#assert_trust kernel NLA.MF18.selected_spectrum_count
#print axioms NLA.MF18.stein_identity
#assert_trust kernel NLA.MF18.stein_identity
#print axioms NLA.MF18.simple_unit_root_pairing
#assert_trust kernel NLA.MF18.simple_unit_root_pairing
#print axioms NLA.MF18.generalized_stein_pairing
#assert_trust kernel NLA.MF18.generalized_stein_pairing
#print axioms NLA.MF18.stable_space_dimension
#assert_trust kernel NLA.MF18.stable_space_dimension
#print axioms NLA.MF18.stable_space_in_kernel
#assert_trust kernel NLA.MF18.stable_space_in_kernel
#print axioms NLA.MF18.stein_rank_lower_bound
#assert_trust kernel NLA.MF18.stein_rank_lower_bound
#print axioms NLA.MF18.full_complex_rank
#assert_trust kernel NLA.MF18.full_complex_rank
#print axioms NLA.MF18.canonical_full_complex_rank
#assert_trust kernel NLA.MF18.canonical_full_complex_rank
