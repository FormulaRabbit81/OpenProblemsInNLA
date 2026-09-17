/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Partial finite-pole-prefix checks only. Six original public obligations remain.
-/
import NLA.SF01.RidgeChecks
import NLA.SF01.PoleResidues

set_option autoImplicit false
set_option leancert.trust "kernel"

#print axioms NLA.SF01.poleMatrix_isHermitian
#assert_trust kernel NLA.SF01.poleMatrix_isHermitian
#print axioms NLA.SF01.pole_energy
#assert_trust kernel NLA.SF01.pole_energy
#print axioms NLA.SF01.poleVector_zero_pos
#assert_trust kernel NLA.SF01.poleVector_zero_pos
#print axioms NLA.SF01.pole_energy_pos
#assert_trust kernel NLA.SF01.pole_energy_pos
#print axioms NLA.SF01.pole_positive_definite
#assert_trust kernel NLA.SF01.pole_positive_definite
#print axioms NLA.SF01.orthogonal_of_unitary_real
#assert_trust kernel NLA.SF01.orthogonal_of_unitary_real
#print axioms NLA.SF01.pole_diagonalization_exists
#assert_trust kernel NLA.SF01.pole_diagonalization_exists
#print axioms NLA.SF01.orthogonal_transpose_dot
#assert_trust kernel NLA.SF01.orthogonal_transpose_dot
#print axioms NLA.SF01.poleMatrix_first_column
#assert_trust kernel NLA.SF01.poleMatrix_first_column
#print axioms NLA.SF01.pole_auxiliary_solve
#assert_trust kernel NLA.SF01.pole_auxiliary_solve
#print axioms NLA.SF01.pole_auxiliary_dot
#assert_trust kernel NLA.SF01.pole_auxiliary_dot
#print axioms NLA.SF01.pole_diagonalized_solve
#assert_trust kernel NLA.SF01.pole_diagonalized_solve
#print axioms NLA.SF01.pole_residue_normalization
#assert_trust kernel NLA.SF01.pole_residue_normalization
#print axioms NLA.SF01.reciprocal_weights_nonnegative
#assert_trust kernel NLA.SF01.reciprocal_weights_nonnegative
#print axioms NLA.SF01.reciprocalWeights_sum
#assert_trust kernel NLA.SF01.reciprocalWeights_sum
