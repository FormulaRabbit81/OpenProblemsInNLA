import Challenge
open NLA.PF02
#synth DiscreteTopology Bool
#synth TopologicalSpace (FactorTuple 6 6 3)
#synth TopologicalSpace (Factorization witnessM 3)
#synth TopologicalSpace (OrbitSpace witnessM 3)
#print Matrix.PosSemidef
#print Matrix.rank
#print NLA.PF02.Congruent
#print NLA.PF02.IsPSDRank
#print NLA.PF02.AllMinimalOrbitsConnected
#check isQuotientMap_quot_mk
#check continuous_quot_lift
#check Matrix.posSemidef_iff_dotProduct_mulVec
#check NLA.PF02.witness_data
#print axioms NLA.PF02.witness_data
#check NLA.PF02.witness_factorizations
#print axioms NLA.PF02.witness_factorizations
#check NLA.PF02.witness_minimal_rank
#print axioms NLA.PF02.witness_minimal_rank
#check NLA.PF02.orbit_semantics
#print axioms NLA.PF02.orbit_semantics
#check NLA.PF02.orientation_nonvanishing
#print axioms NLA.PF02.orientation_nonvanishing
#check NLA.PF02.orientation_preserved
#print axioms NLA.PF02.orientation_preserved
#check NLA.PF02.quotient_separation
#print axioms NLA.PF02.quotient_separation
#check NLA.PF02.witness_disconnected
#print axioms NLA.PF02.witness_disconnected
#check NLA.PF02.canonical_counterexample
#print axioms NLA.PF02.canonical_counterexample
