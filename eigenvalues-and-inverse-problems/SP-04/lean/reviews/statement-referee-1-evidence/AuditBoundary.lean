import Challenge
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Polynomial.Roots

open scoped Matrix
open NLA.SP04

#print Feasible
#print frobeniusSq
#print frobeniusNorm
#print Stationary
#print stationaryPairs
#print UniqueLeastStationary
#print IsNearest
#print RegularData
#print GenericSelectionRule
#print AllGenericSelectionRules
#print Orthogonal
#print HasSVD
#print Admissible
#print counterexampleFamily
#print SelectionFails

#check numerical_bounds
#check diagonal_stationary_iff
#check diagonal_counterexample
#check diagonal_finite
#check orthogonal_transport
#check spectral_family
#check regular_svd
#check open_family_counterexamples
#check algebraic_avoidance
#check generic_counterexamples
#check canonical_counterexample

#synth TopologicalSpace (Mat 3)
#synth T2Space (Mat 3)
#reduce Fintype.card (Fin 3 × Fin 3)
#check Matrix.IsHermitian.spectral_theorem
#check Matrix.IsHermitian.splits_charpoly
#check Matrix.IsHermitian.roots_charpoly_eq_eigenvalues
#check MvPolynomial.funext_set
#check MvPolynomial.funext
#check Polynomial.finite_setOfPred_isRoot
#check Matrix.kronecker
#check Continuous.matrix_det
#check Matrix.frobenius_norm_def
