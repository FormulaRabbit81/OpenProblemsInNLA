# Pinned source APIs and planned reuse

Lean 4.33.1; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Source inspection is distinct from compilation or verification.

- `Matrix.toEuclideanLin` and `LinearMap.singularValues` define the genuine decreasing, nonnegative, zero-extended Euclidean singular values. Accepted MI-13 `gram_charpoly` and `unitary_singular_invariance` show the exact Gram characteristic-polynomial/ordered-eigenvalue transport with multiplicities. Prefer existing APIs and the minimum reusable dependency closure; do not copy the unrelated commutator/SVD proof development.
- `CFC.sqrt`, `CFC.sqrt_mul_sqrt_self`, `IsStrictlyPositive.sqrt`, and `Matrix.isStrictlyPositive_iff_posDef` provide actual roots and invertibility. `MatrixOrder` and the actual L2 operator scope are explicitly used. No matrix-square-root smoothness is needed.
- `eigenvalue_mem_ball` and `Matrix.IsHermitian.posDef_iff_eigenvalues_pos` give positivity from the exact Q diagonal margin. The margin is 3/4 throughout the one 1/16 box; no eigenvalue approximation or subdivision.
- `Matrix.mulVecLin.toContinuousLinearMap` gives the candidate derivative maps on the actual finite real coordinate spaces. Their equality to strict derivatives is a contract, not a definition. `HasStrictFDerivAt.toOpenPartialHomeomorph`, `eventually_right_inverse` and `localInverse_continuousAt` provide the genuine local inverse once the actual derivative has a continuous linear equivalence.
- `Matrix.det_fromBlocks₁₁` and `Matrix.det_one_add_mul_comm` supply Schur and determinant-product reversal. Positivity/invertibility of the actual Schur pivots is an explicit goal. The proof uses no assumption that P and Q commute.
- `Matrix.mem_unitaryGroup_iff'` bridges the canonical one-sided UᴴU=I to the established unitary group. Do not add a separate redundant square-unitarity axiom or narrow the canonical predicate to a special class of U.
- `Matrix.fromBlocks`, `Matrix.fromCols`, `Matrix.fromRows`, `Matrix.reindex` and nested `finSumFinEquiv` are actual block combinators. They avoid manual unsafe indexing or a proof-bearing alternative dimension definition.
- LeanCert kernel-mode `interval_auto` patterns were read in accepted MI-13 ElementaryBounds and the retained Forsythe numerical statement boundary. SP-15's planned scalar certificate is exact rational data and must enter the box/positivity proof. No LeanCert invocation occurred here.

The new finite data are nine explicit polynomial coordinates, a 9×10 derivative, its 9×9 first-column minor, and rational L,U. Prove L·U equals that minor entrywise, triangularity and the diagonal product; avoid permutation-expanding a 9×9 determinant. Actual derivative formation remains required before that certificate can be used analytically.

The draft has no proof implementation to review for final reuse/quality. Later helpers must be searched against these pinned libraries before rederiving known facts.
