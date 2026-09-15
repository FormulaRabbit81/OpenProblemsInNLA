import Challenge
set_option pp.universes true
#print NLA.IE17.spectralNorm
#print NLA.IE17.IsOptimalError
#print NLA.IE17.IsLSMRIterate
#print NLA.IE17.IsTerminatingLSMRRun
#print NLA.IE17.IsMoorePenrose
#print NLA.IE17.IsApproximation
#print NLA.IE17.OptimalErrorsNonincreasing
#print NLA.IE17.ApproximationErrorsNonincreasing
#print axioms NLA.IE17.spectralNorm
#print axioms NLA.IE17.IsOptimalError
#print axioms NLA.IE17.IsApproximation
#check NLA.IE17.spectralNorm_semantics
#check NLA.IE17.witness_full_column_rank
#check NLA.IE17.exact_lsmr_run
#check NLA.IE17.optimal_errors
#check NLA.IE17.approximation_values
#check NLA.IE17.terminal_errors_zero
#check NLA.IE17.both_errors_increase
#check NLA.IE17.canonical_counterexamples
