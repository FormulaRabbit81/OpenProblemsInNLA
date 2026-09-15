import Solution

noncomputable section

namespace NLA.PF02

set_option leancert.trust "kernel"

theorem referee1_witness_data :
    (∀ i j, 0 < witnessM i j) ∧ witnessM.det = 8192 ∧ witnessM.rank = 6 ∧
    (rowCoordinates (witnessFactors 1)).det = 32 ∧
    (rowCoordinates (witnessFactors (-1))).det = -32 := NLA.PF02.witness_data

#assert_trust kernel referee1_witness_data

#print axioms referee1_witness_data

theorem referee1_witness_factorizations :
    IsFactorization witnessM (witnessTuple 1) ∧
    IsFactorization witnessM (witnessTuple (-1)) ∧
    (∀ i, (witnessFactors 1 i).PosDef) ∧
    (∀ i, (witnessFactors (-1) i).PosDef) := NLA.PF02.witness_factorizations

#assert_trust kernel referee1_witness_factorizations

#print axioms referee1_witness_factorizations

theorem referee1_witness_minimal_rank : IsPSDRank witnessM 3 := NLA.PF02.witness_minimal_rank

#assert_trust kernel referee1_witness_minimal_rank

#print axioms referee1_witness_minimal_rank

theorem referee1_orbit_semantics {p q k : ℕ} (M : Mat p q) :
    Topology.IsQuotientMap (@Quot.mk (Factorization M k) (@Congruent p q k M)) ∧
    (∀ F G : Factorization M k,
      Quot.mk (@Congruent p q k M) F = Quot.mk (@Congruent p q k M) G ↔ Congruent F G) := NLA.PF02.orbit_semantics M

#assert_trust kernel referee1_orbit_semantics

#print axioms referee1_orbit_semantics

theorem referee1_orientation_nonvanishing :
    ∀ F : Factorization witnessM 3, orientationDet F ≠ 0 := NLA.PF02.orientation_nonvanishing

#assert_trust kernel referee1_orientation_nonvanishing

#print axioms referee1_orientation_nonvanishing

theorem referee1_orientation_preserved :
    ∀ F G : Factorization witnessM 3, Congruent F G →
      (0 < orientationDet F ↔ 0 < orientationDet G) := NLA.PF02.orientation_preserved

#assert_trust kernel referee1_orientation_preserved

#print axioms referee1_orientation_preserved

theorem referee1_quotient_separation :
    ∃ f : OrbitSpace witnessM 3 → Bool, Continuous f ∧ Function.Surjective f := NLA.PF02.quotient_separation

#assert_trust kernel referee1_quotient_separation

#print axioms referee1_quotient_separation

theorem referee1_witness_disconnected :
    ¬ IsConnected (Set.univ : Set (OrbitSpace witnessM 3)) := NLA.PF02.witness_disconnected

#assert_trust kernel referee1_witness_disconnected

#print axioms referee1_witness_disconnected

theorem referee1_canonical_counterexample : ¬ AllMinimalOrbitsConnected := NLA.PF02.canonical_counterexample

#assert_trust kernel referee1_canonical_counterexample

#print axioms referee1_canonical_counterexample

#assert_trust kernel thirty_two_pos

#print axioms thirty_two_pos

#assert_trust kernel witnessFactors_posDef

#print axioms witnessFactors_posDef

#assert_trust kernel witness_trace

#print axioms witness_trace

#assert_trust kernel explicit_factorizations

#print axioms explicit_factorizations

#assert_trust kernel witness_coordinate_det

#print axioms witness_coordinate_det

#assert_trust kernel witness_matrix_det

#print axioms witness_matrix_det

#assert_trust kernel trace_coordinate_identity

#print axioms trace_coordinate_identity

#assert_trust kernel factorization_coordinate_identity

#print axioms factorization_coordinate_identity

#assert_trust kernel congruence_covariance

#print axioms congruence_covariance

#assert_trust kernel rowCoordinates_congruence

#print axioms rowCoordinates_congruence

#assert_trust kernel congruenceCoordinates_det

#print axioms congruenceCoordinates_det

#assert_trust kernel orientation_congruent

#print axioms orientation_congruent

#assert_trust kernel changeBasis_preserves_factorization

#print axioms changeBasis_preserves_factorization

#assert_trust kernel changeBasis_congruent

#print axioms changeBasis_congruent

#assert_trust kernel congruent_iff_changeBasis

#print axioms congruent_iff_changeBasis

#assert_trust kernel trace_factor_rank_le

#print axioms trace_factor_rank_le

#assert_trust kernel minimal_three_of_rank_six

#print axioms minimal_three_of_rank_six

#assert_trust kernel actual_orbit_eq_iff

#print axioms actual_orbit_eq_iff

#assert_trust kernel all_orientation_nonzero

#print axioms all_orientation_nonzero

#assert_trust kernel continuous_fiberSign

#print axioms continuous_fiberSign

#assert_trust kernel continuous_orbitSign

#print axioms continuous_orbitSign

#assert_trust kernel orbitSign_surjective

#print axioms orbitSign_surjective

#assert_trust kernel orbit_quotient_disconnected

#print axioms orbit_quotient_disconnected

#synth DiscreteTopology Bool

#synth TopologicalSpace (Factorization witnessM 3)

#synth TopologicalSpace (OrbitSpace witnessM 3)

end NLA.PF02
