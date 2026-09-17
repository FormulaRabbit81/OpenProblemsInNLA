# MI-13 operator norm: semantic route before source

This bounded author task implements only the exact frozen
`operator_norm_semantics` contract. It does not complete MI-13. The 13 frozen
inputs were rehashed unchanged before this file was written. The root's
accepted statement freeze remains the mathematical boundary.

For every complex rectangular matrix `A : Rect m n`, including `m = 0` and
`n = 0`, the target is the conjunction

1. the continuous linear map's actual Euclidean operator norm equals the
   first actual, decreasing, zero-extended singular value;
2. this operator norm is zero exactly when every matrix entry is zero;
3. the usual application bound holds for every Euclidean domain vector.

The matrix function-space supremum norm is never used as the matrix's norm.
There is no extra numerical certificate here. Existing kernel-mode LeanCert
settings remain active; all arithmetic in this module is symbolic. The
genuinely needed half certificate belongs to the separate averaging proof.

Let `T = euclideanLin A`, let `G = adjoint T ∘ T`, and use the pinned
orthonormal eigenbasis `b` for the symmetric operator `G`. Its eigenvalues
are exactly `singularValue A i.val ^ 2`. The pinned diagonal-coordinate
formula and adjoint identity give the finite energy identity

`‖T x‖² = Σ i, singularValue A i.val² * ‖b.repr x i‖²`.

This identity follows by transporting `inner x (G x)` through the isometry
`b.repr`, expanding the Euclidean inner product as a finite sum, and taking
real parts. Complex conjugation is handled by the actual complex inner
product; coordinates and matrix entries have no reality restriction.

Nonnegativity and antitonicity from the accepted `SingularSemantics` module
bound every singular-value square by the first square. Parseval, expressed
as `EuclideanSpace.norm_sq_eq` after the isometry, gives
`‖T x‖² ≤ singularValue A 0² * ‖x‖²`. Taking the order equivalence between
nonnegative squares gives the application bound with this constant, hence
the operator norm's upper bound.

If `n > 0`, use the basis vector with index zero. Its sole nonzero basis
coordinate is one, so the same energy identity gives an image norm equal
to the first singular value. Its domain norm is one, which gives the
reverse operator-norm bound. If `n = 0`, the zero-extension theorem gives
the first singular value zero, and operator-norm nonnegativity provides
the reverse bound. Nothing requires a nonzero codomain, invertibility,
positive singular values, or distinct eigenvalues.

For zero equivalence, `norm_eq_zero` first gives the zero continuous linear
map. Injectivity of the finite-dimensional linear-to-continuous-linear
equivalence and the matrix-to-Euclidean-linear equivalence gives the zero
matrix. The converse uses their zero-preservation. The final application
bound is the existing continuous operator-norm inequality.

Only `SingularSemantics` and its frozen `Definitions` dependency are needed.
There is no import of Challenge, full SVD, unitary invariance or rectangular
padding. This avoids circular use of later MI-13 contracts.

The author does not run Lean, Lake, caches, Git, or publication commands.
The candidate must be compiled by the root's single-thread, 4096 MiB local
runner. Source inspection and header/hash checks are not elaboration or a
kernel/Comparator success claim.

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology. Substantial OpenAI Codex assistance.
Nobori's original question, Audenaert's refined theorem and the repository
reduction retain their mathematical attribution.
