import Solution
set_option leancert.trust "kernel"
open NLA.PF02
#synth DiscreteTopology Bool
#synth TopologicalSpace (Factorization witnessM 3)
#synth TopologicalSpace (OrbitSpace witnessM 3)
#assert_trust kernel NLA.PF02.witness_data
#print axioms NLA.PF02.witness_data
#check NLA.PF02.witness_data
#assert_trust kernel NLA.PF02.witness_factorizations
#print axioms NLA.PF02.witness_factorizations
#check NLA.PF02.witness_factorizations
#assert_trust kernel NLA.PF02.witness_minimal_rank
#print axioms NLA.PF02.witness_minimal_rank
#check NLA.PF02.witness_minimal_rank
#assert_trust kernel NLA.PF02.orbit_semantics
#print axioms NLA.PF02.orbit_semantics
#check NLA.PF02.orbit_semantics
#assert_trust kernel NLA.PF02.orientation_nonvanishing
#print axioms NLA.PF02.orientation_nonvanishing
#check NLA.PF02.orientation_nonvanishing
#assert_trust kernel NLA.PF02.orientation_preserved
#print axioms NLA.PF02.orientation_preserved
#check NLA.PF02.orientation_preserved
#assert_trust kernel NLA.PF02.quotient_separation
#print axioms NLA.PF02.quotient_separation
#check NLA.PF02.quotient_separation
#assert_trust kernel NLA.PF02.witness_disconnected
#print axioms NLA.PF02.witness_disconnected
#check NLA.PF02.witness_disconnected
#assert_trust kernel NLA.PF02.canonical_counterexample
#print axioms NLA.PF02.canonical_counterexample
#check NLA.PF02.canonical_counterexample
#assert_trust kernel NLA.PF02.thirty_two_pos
#print axioms NLA.PF02.thirty_two_pos
#assert_trust kernel NLA.PF02.witnessFactors_posDef
#print axioms NLA.PF02.witnessFactors_posDef
#assert_trust kernel NLA.PF02.witness_trace
#print axioms NLA.PF02.witness_trace
#assert_trust kernel NLA.PF02.witness_coordinate_det
#print axioms NLA.PF02.witness_coordinate_det
#assert_trust kernel NLA.PF02.witness_matrix_det
#print axioms NLA.PF02.witness_matrix_det
#assert_trust kernel NLA.PF02.trace_coordinate_identity
#print axioms NLA.PF02.trace_coordinate_identity
#assert_trust kernel NLA.PF02.factorization_coordinate_identity
#print axioms NLA.PF02.factorization_coordinate_identity
#assert_trust kernel NLA.PF02.congruence_covariance
#print axioms NLA.PF02.congruence_covariance
#assert_trust kernel NLA.PF02.rowCoordinates_congruence
#print axioms NLA.PF02.rowCoordinates_congruence
#assert_trust kernel NLA.PF02.congruenceCoordinates_det
#print axioms NLA.PF02.congruenceCoordinates_det
#assert_trust kernel NLA.PF02.orientation_congruent
#print axioms NLA.PF02.orientation_congruent
#assert_trust kernel NLA.PF02.changeBasis_preserves_factorization
#print axioms NLA.PF02.changeBasis_preserves_factorization
#assert_trust kernel NLA.PF02.changeBasis_congruent
#print axioms NLA.PF02.changeBasis_congruent
#assert_trust kernel NLA.PF02.congruent_iff_changeBasis
#print axioms NLA.PF02.congruent_iff_changeBasis
#assert_trust kernel NLA.PF02.trace_factor_rank_le
#print axioms NLA.PF02.trace_factor_rank_le
#assert_trust kernel NLA.PF02.minimal_three_of_rank_six
#print axioms NLA.PF02.minimal_three_of_rank_six
#assert_trust kernel NLA.PF02.congruent_refl
#print axioms NLA.PF02.congruent_refl
#assert_trust kernel NLA.PF02.congruent_symm
#print axioms NLA.PF02.congruent_symm
#assert_trust kernel NLA.PF02.congruent_trans
#print axioms NLA.PF02.congruent_trans
#assert_trust kernel NLA.PF02.actual_orbit_eq_iff
#print axioms NLA.PF02.actual_orbit_eq_iff
#assert_trust kernel NLA.PF02.continuous_orientationDet
#print axioms NLA.PF02.continuous_orientationDet
#assert_trust kernel NLA.PF02.continuous_fiberSign
#print axioms NLA.PF02.continuous_fiberSign
#assert_trust kernel NLA.PF02.fiberSign_congruent
#print axioms NLA.PF02.fiberSign_congruent
#assert_trust kernel NLA.PF02.continuous_orbitSign
#print axioms NLA.PF02.continuous_orbitSign
#assert_trust kernel NLA.PF02.orbitSign_surjective
#print axioms NLA.PF02.orbitSign_surjective
#assert_trust kernel NLA.PF02.orbit_quotient_disconnected
#print axioms NLA.PF02.orbit_quotient_disconnected
