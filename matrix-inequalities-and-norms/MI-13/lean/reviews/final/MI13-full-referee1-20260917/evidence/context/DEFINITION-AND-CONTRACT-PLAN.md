# MI-13 definitions and contracts chosen before Lean statement code

Author: George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology. Drafted with OpenAI Codex assistance by
`/root/mi04_independent_referee`. This agent becomes the statement author, not
an independent referee for these statements. The already reviewed informal
route does not approve this future Lean boundary automatically.

## Concrete definitions

Use finite `Fin` indices throughout the target. Define `Rect m n`, `Square r`
and genuine complex Euclidean vector spaces. Define `euclideanLin A` using
`Matrix.toEuclideanLin` and `euclideanCLM A` using the pinned finite-dimensional
conversion to continuous linear maps. The operator norm is explicitly the norm
of this CLM, never the default norm of a matrix.

Flatten a matrix by `(i,j) ↦ A i j` into
`EuclideanSpace ℂ (Fin m × Fin n)`. Its Euclidean norm is the Frobenius norm.
Define the square Hilbert–Schmidt product using that actual inner product.
Define singular values directly as `(euclideanLin A).singularValues k` and
ordered Gram eigenvalues using its actual `adjoint ∘ euclideanLin A` and the
pinned sorted-eigenvalue construction. No spectrum or norm is assigned a desired
value by definition.

Define a unitary square matrix by both actual conjugate-transpose inverse
identities. Define the real singular-value diagonal, normalized right-singular
vector images, and the set of positive singular-value indices. A predicate
`GramBasis A v` only records the actual Gram eigenvector equations for a given
orthonormal basis; its existence is a separate required conclusion.

Define `[X,Y]=XY−YX`, `T_X(Y)=[X*,[X,Y]]`, and `J_X(Y)=[X*,Y*]` by actual
products. Define an explicit matrix of commutator coefficients on the pair
indices; its associated Euclidean CLM must be proved to act on flattened
matrices as the actual commutator. This avoids pretending the entrywise matrix
norm is a Hilbert-space norm. All adjoint/flattening identities remain required.
Define the first-entry function by the `(0,0)` entry when the dimension is
positive, and zero at dimension zero; no dummy dimension premise enters the
original target.

Choose sum-index block padding, reindexed by the actual equivalence
`Fin m ⊕ Fin n ≃ Fin (m+n)`: A and C occupy the upper-right block, B the
lower-left block; all other blocks are zero. This avoids the m≤n/n≤m split.
It changes no target constant because the square bound is dimension independent.
Preservation of all actual singular values, including padded zeros, is a proof
obligation, not a definition. Frobenius/operator norm preservation and the
exact three-factor product identity are separate obligations.

Define only the two fixed 2×2 sharpness matrices and the universal diagonal
unit-circle lift used in the averaging construction. Definitions must contain
no desired inequality, existence oracle, added axiom or proof placeholders.

## Planned complete contracts

Every numbered item becomes a deliberately unproved independent Challenge
declaration. Hypotheses on intermediate bases/unitaries are local helper inputs;
their unrestricted existence is separately required. None enters the canonical
target as an extra premise.

1. `frobenius_semantics`: squared Frobenius norm equals the full finite sum of
   squared complex entry norms and the real trace of the actual Gram matrix;
   the norm is nonnegative and vanishes exactly on the zero matrix.
2. `frobenius_linear_bounds`: exact complex scaling and the triangle inequality.
3. `operator_norm_semantics`: actual operator norm equals singular value zero,
   vanishes exactly for the zero matrix, and bounds the actual map on every vector.
4. `singular_values_semantics`: nonnegativity, antitonicity and zero extension
   at indices at least the number of columns.
5. `singular_values_gram`: every in-range squared singular value equals the
   corresponding actual ordered Gram eigenvalue.
6. `ordered_gram_basis`: existence of a full ordered orthonormal Gram eigenbasis.
7. `positive_image_orthonormal`: normalized images restricted to positive
   singular-value indices are orthonormal, without requiring all values positive.
8. `zero_singular_image`: every zero-value Gram eigenvector has zero image.
9. `positive_image_extension`: extend the partially indexed orthonormal images
   to a complete basis while fixing their positive indices; no separate rank count.
10. `full_singular_vector_bases`: complete left/right orthonormal bases satisfy
    `A v_i = s_i u_i` at every index, including zeros.
11. `full_svd`: actual unitary matrices U,V exist with
    `A = U diag(actual singular values) V*`, for every square A of every rank.
12. `unitary_norm_invariance`: actual Frobenius and operator norms are invariant
    under left/right unitary multiplication for rectangular matrices.
13. `unitary_singular_invariance`: every actual zero-extended singular value is
    invariant under the same unitary multiplications.
14. `hilbert_schmidt_semantics`: flattening is injective and linear, the inner
    product is the Gram trace, and the explicit commutator CLM acts correctly.
15. `commutator_adjoint`: the actual Hilbert CLM adjoint is ad(X*), with the
    exact trace/inner-product adjoint identity and energy identity for T.
16. `commutator_conjugate_symmetry`: J is conjugate-linear, J²=−T, TJ=JT,
    Y is orthogonal to JY, and `‖JY‖F=‖[X,Y]‖F`.
17. `commutator_spectral_maximum`: for square order at least two there exist a
    nonnegative real λ and nonzero Y with T Y=λY and the universal bound
    `‖[X,Z]‖F² ≤ λ‖Z‖F²`. Use the actual Rayleigh maximum; no r² eigenbasis needed.
18. `positive_eigenvector_pair`: at any positive real eigenvalue, JY is a
    nonzero eigenvector orthogonal to nonzero Y, with the exact norm-square identity.
19. `eigenspace_functional_kernel`: every complex-linear scalar functional has
    a nonzero kernel vector in that positive-eigenvalue space, constructed from Y,JY.
20. `two_coordinate_bound`: the universal complex two-coordinate inequality in
    NUMERICAL_TARGETS, proved symbolically.
21. `off_corner_coefficient_bound`: for any nonnegative descending sequence s
    and `(i,j)≠(0,0)`, `s_i²+s_j²≤s_0²+s_1²`.
22. `svd_corner_functional`: the transformed commutator's first entry is the
    value of an actual complex-linear scalar functional on all matrices.
23. `cancelled_svd_bound`: given the actual SVD and vanishing first transformed
    commutator entry, prove the desired refined squared bound on that vector.
24. `refined_commutator_bound`: full unconditional complex square commutator
    inequality for every order at least two and every pair of matrices.
25. `half_certificate`: exact positive half and its sum identity; planned
    kernel LeanCert positivity, genuinely consumed by averaging.
26. `unit_circle_lift`: exact unit-modulus and average identities for every
    scalar in [0,1], using a symbolic square root.
27. `two_unitary_average`: every square contraction is half the sum of two
    actual unitaries, including singular and zero contractions.
28. `frobenius_average_bound`: the squared norm of the half-sum is bounded by
    the half-sum of squared norms.
29. `unitary_middle_bound`: the exact three-factor squared bound when the middle
    factor is unitary, using the actual right-multiplication commutator identity.
30. `contraction_middle_bound`: the same bound for every contraction.
31. `square_middle_bound`: the full square bound with the actual middle operator
    norm factor, separating B=0 before division and retaining every rank.
32. `padding_product`: the padded three-factor difference is the upper block
    embedding of the genuine rectangular difference.
33. `padding_norms`: preserve both actual norms for upper/lower block embeddings.
34. `padding_singular_values`: every actual singular value is preserved under
    upper/lower block zero padding. This includes rank zero/one and both original
    dimension orderings; a block identity alone is not its proof.
35. `canonical_rectangular_bound`: precisely the original MI-13 inequality,
    all m,n≥2 and all complex A,C,B of the original shapes, with no extra premises.
36. `sharpness_example`: exact 2×2 values listed in NUMERICAL_TARGETS.

The draft will therefore propose 36 contracts, with all final semantic and SVD
facts visible. Internal proof helpers may later be added without altering the
frozen contracts. This record authorizes no proof implementation or compilation.
