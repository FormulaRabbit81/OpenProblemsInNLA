import Challenge
open NLA.PF02
#synth DiscreteTopology Bool
#synth TopologicalSpace (Factorization witnessM 3)
#synth TopologicalSpace (OrbitSpace witnessM 3)
#print NLA.PF02.IsFactorization
#print NLA.PF02.IsPSDRank
#print NLA.PF02.Congruent
#print NLA.PF02.OrbitSpace
#print NLA.PF02.AllMinimalOrbitsConnected
#check NLA.PF02.witness_data
#check NLA.PF02.witness_factorizations
#check NLA.PF02.witness_minimal_rank
#check NLA.PF02.orbit_semantics
#check NLA.PF02.orientation_nonvanishing
#check NLA.PF02.orientation_preserved
#check NLA.PF02.quotient_separation
#check NLA.PF02.witness_disconnected
#check NLA.PF02.canonical_counterexample
