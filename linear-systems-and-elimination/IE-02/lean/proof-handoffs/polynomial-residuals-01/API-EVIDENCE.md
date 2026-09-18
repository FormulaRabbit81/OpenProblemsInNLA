# Polynomial residual and GMRES candidate: primary API evidence

Mathlib pin 0df444a360eaa60ab8c11dca51a86af692955474. All sources were inspected
read-only; original primary bindings precede coding and additional exact file
hashes appear in HANDOFF.json. No compiler or cached-output provenance claim
is made by this author handoff.

| Source / API | Use in the candidate |
| --- | --- |
| Polynomial/AlgebraMap.lean:523, aeval_eq_sum_range' | Exact matrix polynomial evaluation as the finite coefficient sum through degree k. Valid for arbitrary semiring targets with the algebra structure, including the zero-size matrix ring. |
| Polynomial/Eval/Coeff.lean:57, coeff_zero_eq_eval_zero | Transports the frozen p(0)=1 normalization to the coefficient at zero. |
| BigOperators/Fin.lean:39, Finset.prod_range and its sum version; :76 Fin.prod_univ_succ and generated Fin.sum_univ_succ | Reindex the coefficient range by Fin(k+1), then split off index zero and identify the Fin k tail. Existing Fin.sum_univ_eq_sum_range is the inverse range reindexing already used in prior IE02 modules. |
| Polynomial/Degree/Defs.lean:142, degree_le_of_natDegree_le and converse | Changes between the exact frozen degree bound and the natural-degree inequalities needed for finite expansion and monomial estimates. |
| Polynomial/Degree/Defs.lean:365, natDegree_C_mul_X_pow_le | Bounds each explicit residual-polynomial term even if its coefficient is zero. |
| Polynomial/Degree/Defs.lean:386, degree_sum_le; Data/Finset/Lattice/Fold.lean:99-105, Finset.sup_le | Bounds the finite sum by k, including an empty sum. |
| Polynomial/Degree/Defs.lean:526, degree_sub_le | The explicit normalized polynomial 1 minus that sum has the same degree bound. |
| Polynomial/Eval/Defs.lean:348, eval_finsetSum, and the evaluation rules for subtraction, constants and powers | Evaluation at zero of each positive-power term vanishes. |
| Polynomial/AlgebraMap.lean:290-302, aeval_C and aeval_X; standard map_sub/map_sum/map_mul/map_pow | Evaluate the constructed polynomial in the actual matrix algebra. |
| Algebra/Algebra/Defs.lean:279, algebraMap_eq_smul_one; scalar multiplication associativity | Convert the constant embedding times a matrix power to c_j • A^(j+1). |
| Project AffineMinima.lean, affine_operator_minimum / affine_vector_minimum | Reuse actual attained affine norms for Y=1 and arbitrary possibly dependent matrix-power directions. No nearest-point or minimax assumption is introduced. |
| Analysis/Normed/Operator/Basic.lean:237, ContinuousLinearMap.le_opNorm | Bound the operator-minimizing polynomial's residual on a unit vector by its attained operator norm. |

The universal residual parameterization and value-set identity are supporting
lemmas, each genuinely used by the exact frozen exports. The value-set result
is proved elementwise in both directions before applying sInf. It is stated
for an arbitrary function on matrices so the same witness proof covers both
actual norm value sets. This changes no frozen definition.

No low-degree remainder, polynomial divisibility, independence of powers,
invertibility, spectral decomposition, or oracle is assumed. The direct
coefficient expansion already gives precisely the two frozen residual
existentials. No Toeplitz/NilpotentInverse import is introduced because these
bridges hold for arbitrary matrices. JordanDirections was read only to avoid
reimplementing its already assigned contract; it is not a dependency.
