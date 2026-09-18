/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agents; module headers retain individual code
attribution and adaptation credits. Ghabries--Abbas--Mourad--Assi retain credit for
the original question, and Dinh--Dumitru--Franco for the published Heron comparison.
The imports expose all 22 unchanged local289 contracts without redeclaring them.
This file requests explicit axiom and kernel-trust checks; execution evidence is
recorded separately and is never inferred merely from the presence of commands.
-/
import NLA.MI24.Complement
import NLA.MI24.FiniteSemantics

set_option autoImplicit false
set_option leancert.trust "kernel"

#print axioms NLA.MI24.young_weight_interval
#assert_trust kernel NLA.MI24.young_weight_interval
#print axioms NLA.MI24.spectral_power_inverse
#assert_trust kernel NLA.MI24.spectral_power_inverse
#print axioms NLA.MI24.geometric_congruence
#assert_trust kernel NLA.MI24.geometric_congruence
#print axioms NLA.MI24.matrix_means_posdef
#assert_trust kernel NLA.MI24.matrix_means_posdef
#print axioms NLA.MI24.power_half_fixed_point
#assert_trust kernel NLA.MI24.power_half_fixed_point
#print axioms NLA.MI24.power_half_sqrt_q
#assert_trust kernel NLA.MI24.power_half_sqrt_q
#print axioms NLA.MI24.furuta_half_power
#assert_trust kernel NLA.MI24.furuta_half_power
#print axioms NLA.MI24.weighted_geometric_trace
#assert_trust kernel NLA.MI24.weighted_geometric_trace
#print axioms NLA.MI24.trace_young_half
#assert_trust kernel NLA.MI24.trace_young_half
#print axioms NLA.MI24.heron_trace_comparison
#assert_trust kernel NLA.MI24.heron_trace_comparison
#print axioms NLA.MI24.positive_schatten_monotone
#assert_trust kernel NLA.MI24.positive_schatten_monotone
#print axioms NLA.MI24.positive_schatten_triangle
#assert_trust kernel NLA.MI24.positive_schatten_triangle
#print axioms NLA.MI24.positive_schatten_smul
#assert_trust kernel NLA.MI24.positive_schatten_smul
#print axioms NLA.MI24.positive_infinity_monotone
#assert_trust kernel NLA.MI24.positive_infinity_monotone
#print axioms NLA.MI24.finite_schatten_semantics
#assert_trust kernel NLA.MI24.finite_schatten_semantics
#print axioms NLA.MI24.infinity_schatten_semantics
#assert_trust kernel NLA.MI24.infinity_schatten_semantics
#print axioms NLA.MI24.heron_comparison_finite
#assert_trust kernel NLA.MI24.heron_comparison_finite
#print axioms NLA.MI24.heron_comparison_infinity
#assert_trust kernel NLA.MI24.heron_comparison_infinity
#print axioms NLA.MI24.lin_comparison
#assert_trust kernel NLA.MI24.lin_comparison
#print axioms NLA.MI24.schatten_complement_finite
#assert_trust kernel NLA.MI24.schatten_complement_finite
#print axioms NLA.MI24.schatten_complement_infinity
#assert_trust kernel NLA.MI24.schatten_complement_infinity
#print axioms NLA.MI24.schattenComplementConjecture
#assert_trust kernel NLA.MI24.schattenComplementConjecture
