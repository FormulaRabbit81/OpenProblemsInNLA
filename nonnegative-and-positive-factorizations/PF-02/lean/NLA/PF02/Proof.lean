/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
The nine exports match the independently reviewed Challenge specification.
-/
import NLA.PF02.Action
import NLA.PF02.Rank
import NLA.PF02.Topology

noncomputable section
namespace NLA.PF02

/-- Literal integer matrix, full ordinary rank, and opposite exact coordinate orientations. -/
theorem witness_data :
    (∀ i j, 0 < witnessM i j) ∧ witnessM.det = 8192 ∧ witnessM.rank = 6 ∧
    (rowCoordinates (witnessFactors 1)).det = 32 ∧
    (rowCoordinates (witnessFactors (-1))).det = -32 := by
  exact witness_numeric_data

/-- Both complete trace factorizations have genuinely positive definite factors. -/
theorem witness_factorizations :
    IsFactorization witnessM (witnessTuple 1) ∧
    IsFactorization witnessM (witnessTuple (-1)) ∧
    (∀ i, (witnessFactors 1 i).PosDef) ∧
    (∀ i, (witnessFactors (-1) i).PosDef) := by
  exact explicit_factorizations

/-- Actual minimum factor size among every positive integer size and every real PSD tuple. -/
theorem witness_minimal_rank : IsPSDRank witnessM 3 := by
  exact minimal_three_of_rank_six witness_numeric_data.2.2.1
    ⟨⟨witnessTuple 1, explicit_factorizations.1⟩⟩

/-- Exact single-congruence orbits with the canonical quotient topology in every dimension. -/
theorem orbit_semantics {p q k : ℕ} (M : Mat p q) :
    Topology.IsQuotientMap (@Quot.mk (Factorization M k) (@Congruent p q k M)) ∧
    (∀ F G : Factorization M k,
      Quot.mk (@Congruent p q k M) F = Quot.mk (@Congruent p q k M) G ↔ Congruent F G) := by
  exact actual_orbit_semantics M

/-- Every factorization of the actual matrix has a nonzero row-coordinate determinant. -/
theorem orientation_nonvanishing :
    ∀ F : Factorization witnessM 3, orientationDet F ≠ 0 := by
  exact all_orientation_nonzero

/-- Every real invertible congruence preserves the sign, throughout the full factorization space. -/
theorem orientation_preserved :
    ∀ F G : Factorization witnessM 3, Congruent F G →
      (0 < orientationDet F ↔ 0 < orientationDet G) := by
  exact orientation_congruent

/-- A genuine continuous surjection from the entire orbit quotient onto a discrete two-point space. -/
theorem quotient_separation :
    ∃ f : OrbitSpace witnessM 3 → Bool, Continuous f ∧ Function.Surjective f := by
  exact ⟨orbitSign, continuous_orbitSign, orbitSign_surjective⟩

/-- Actual disconnectedness in the quotient topology, stronger than absence of a selected path. -/
theorem witness_disconnected :
    ¬ IsConnected (Set.univ : Set (OrbitSpace witnessM 3)) := by
  exact orbit_quotient_disconnected

/-- The complete original universally quantified connectedness claim is false. -/
theorem canonical_counterexample : ¬ AllMinimalOrbitsConnected := by
  intro h
  apply witness_disconnected
  exact h 3 6 6 (by norm_num) (by norm_num) (by norm_num) witnessM
    (fun i j => le_of_lt (witness_data.1 i j))
    (by simpa using witness_data.2.2.1) witness_minimal_rank

#assert_trust kernel witness_data
#assert_trust kernel witness_factorizations
#assert_trust kernel witness_minimal_rank
#assert_trust kernel orbit_semantics
#assert_trust kernel orientation_nonvanishing
#assert_trust kernel orientation_preserved
#assert_trust kernel quotient_separation
#assert_trust kernel witness_disconnected
#assert_trust kernel canonical_counterexample
#print axioms witness_data
#print axioms witness_factorizations
#print axioms witness_minimal_rank
#print axioms orbit_semantics
#print axioms orientation_nonvanishing
#print axioms orientation_preserved
#print axioms quotient_separation
#print axioms witness_disconnected
#print axioms canonical_counterexample

end NLA.PF02
