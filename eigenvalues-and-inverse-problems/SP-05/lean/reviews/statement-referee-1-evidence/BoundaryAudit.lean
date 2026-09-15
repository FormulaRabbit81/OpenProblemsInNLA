import Challenge
import Mathlib
open scoped Matrix
open NLA.SP05
#print NLA.SP05.columnVec
#print NLA.SP05.commutationMatrix
#print NLA.SP05.frobeniusSq
#print NLA.SP05.rayleigh
#print NLA.SP05.jordanMatrix
#print NLA.SP05.sectorValues
#print NLA.SP05.skewExample
#print Matrix.PosDef
#print Matrix.PosSemidef
#print IsLeast
#check NLA.SP05.numerical_bound
#check NLA.SP05.column_vectorization
#check NLA.SP05.skew_witness
#check NLA.SP05.positive_minimizer
#check NLA.SP05.sector_minima
#check NLA.SP05.canonical_result
#check Matrix.vec_bijective
#check Matrix.vec_eq_zero_iff
#check Matrix.kronecker_mulVec_vec
#check Matrix.star_vec_dotProduct_vec
#check Matrix.PosDef.kronecker
#check Matrix.PosDef.inv
#check Matrix.PosDef.isUnit
#check Matrix.PosDef.re_dotProduct_pos
#check Matrix.PosSemidef.re_dotProduct_nonneg
#check Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg
#check Matrix.IsHermitian.mulVec_eigenvectorBasis
#check Matrix.IsHermitian.spectral_theorem
#check Matrix.PosSemidef.conjTranspose_mul_mul_same
#check Matrix.PosSemidef.trace_nonneg
#check CFC.sqrt_unique
#check CFC.sqrt_mul_sqrt_self
#check CFC.abs_sq
#check CFC.posPart_sub_negPart
#check CFC.posPart_mul_negPart
#check CFC.posPart_add_negPart
#check IsSelfAdjoint.hasEigenvector_of_isMaxOn
#check LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional
#check LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
#check IsCompact.exists_isMinOn
#check isCompact_sphere
#synth InnerProductSpace ℝ (EuclideanSpace ℝ (Fin 2 × Fin 2))
#synth InnerProductSpace ℂ (EuclideanSpace ℂ (Fin 2 × Fin 2))
#reduce Fintype.card (Fin 3 × Fin 3)
section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
#check fun (a b : Matrix (Fin 2) (Fin 2) ℂ) (h : b*b=a) (hb : 0≤b) => CFC.sqrt_unique h hb
#check fun (a b : Matrix (Fin 2) (Fin 2) ℝ) (h : b*b=a) (hb : 0≤b) => CFC.sqrt_unique h hb
#check (CFC.abs_sq (A := Matrix (Fin 2) (Fin 2) ℂ))
#check fun (a : Matrix (Fin 2) (Fin 2) ℂ) (ha : IsSelfAdjoint a) => CFC.posPart_add_negPart a ha
#check (Matrix.nonneg_iff_posSemidef (𝕜 := ℂ) (n := Fin 2))
end
