# Pinned primary API bindings for the proposed two modules

Complete source hashes and exact paths are in 02-SOURCE-BINDINGS.json.
All Mathlib files use the frozen pin
0df444a360eaa60ab8c11dca51a86af692955474. These are inspected interfaces,
not a claim of elaborated new code or completed Schur induction.

| Need | Inspected primary source and interface |
|---|---|
| Split off a polynomial constant; shift coefficients | Algebra/Polynomial/Inductions.lean:44 coeff_divX and :51 X_mul_divX_add; Coeff.lean:119 mul_coeff_zero, :145 coeff_X_mul_zero, :259 coeff_X_mul, :334 smul_eq_C_mul |
| Finite matrix action and composition | Analysis/Normed/Lp/Matrix.lean:30 toLpLin, :52 toLpLin_one, :62 toLpLin_mul_same; PiL2.lean:1243 toEuclideanLin is the exponent-two abbreviation |
| Exact conjugate-transpose/adjoint bridge | Analysis/InnerProductSpace/Adjoint.lean:1055 Matrix.toEuclideanLin_conjTranspose_eq_adjoint, :581 LinearMap.adjoint_inner_left |
| Gram energy as a real squared norm | InnerProductSpace/Basic.lean:53 exports norm_sq_eq_re_inner; the field argument will be fixed explicitly to C, as in accepted MaximalSpace |
| Real scalars in the complex inner product | Data/Complex/Basic.lean:226 Complex.re_ofReal_mul and :475 Complex.conj_ofReal; avoid the known generic RCLike mismatch |
| Scalar disk defect | Analysis/Complex/Norm.lean:150 Complex.sq_norm; Data/Complex/Basic.lean:501 star_def, :517 normSq_apply, :572 normSq_conj, :574 normSq_mul, :577 normSq_add |
| Operator bound in both directions | Analysis/Normed/Operator/Basic.lean:199 opNorm_le_bound, :237 le_opNorm; no positive-defect spectral theorem required |
| Nonnegative norm-square conversion | Algebra/Order/GroupWithZero/Basic.lean:705 sq_eq_sq₀ and :715 sq_le_sq₀ |
| Degree and zero high coefficients | Polynomial/Degree/Defs.lean:326 degree_add_le, :330 degree_add_le_of_degree_le, :493 degree_le_iff_coeff_zero; Operations.lean:181 degree_add_eq_right_of_degree_lt, :456 degree_smul_le, :537 degree_mul_X, :674 degree_mul |
| Explicit Bezout witnesses | RingTheory/Coprime/Basic.lean:43 IsCoprime is a two-witness linear combination; :110 IsCoprime.mul_left multiplies the coprime left factors |
| Append and prefix coordinates | Data/Fin/Tuple/Basic.lean:505 init, :516 snoc, :526 snoc_castSucc, :539 snoc_last, :602 snoc_init_self; specify the constant complex dependent family where necessary |
| Restrict the two inverse maps to maximal subspaces | Algebra/Module/Submodule/LinearMap.lean:142 domRestrict, :157 codRestrict, :210 restrict |
| Turn inverse maps into an equivalence | Algebra/Module/Equiv/Basic.lean:484 LinearEquiv.ofLinearMap takes f.comp g=id and g.comp f=id; the older ofLinear spelling is deprecated |
| Transfer dimension without a rank oracle | LinearAlgebra/Dimension/Finrank.lean:116 LinearEquiv.finrank_eq |

Existing project sources are genuinely used: Toeplitz provides the concrete
algebra hom, multiplication, shift nilpotence, action and truncation;
NilpotentInverse provides the explicit two-sided finite inverse and Toeplitz
closure; SchurDefect provides the exact complex matrix identity;
NormAttainment provides an actual unit maximizer; MaximalSpace supplies the
proved kernel/norm equivalence; SchurActiveBlock provides the exact two
coordinate embeddings, norm compression and saturation statement.
Coefficient-vector scalar identities will be proved directly from the frozen
definition via PiLp.ext when not already packaged as project lemmas.

The source plan does not presume any finite CF/Schur interpolation library
theorem, matrix PSD oracle, SVD, desired rank formula, or minimax theorem.
The quoted interpolation lift and submodule equivalence are new obligations
to prove in the two proposed modules. Source/olean presence may be inspected
read-only before implementation; it never establishes new proof success.
