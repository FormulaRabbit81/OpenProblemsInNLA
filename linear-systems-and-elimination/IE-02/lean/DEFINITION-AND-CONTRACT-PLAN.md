# Concrete definition and contract plan before Lean statement code

Author agent /root/ie02_foundation_preflight is a statement author, not an independent referee. The complete finite paper route has a separate nonauthor PASS, but that is not approval of these new Lean statements.

Use actual finite complex matrices, Euclidean vectors, explicit coefficient truncation, and Matrix.toEuclideanLin followed by toContinuousLinearMap for every operator norm. Toeplitz matrices are explicitly p.coeff(i-j) below the diagonal; IsToeplitz only states existence of such a symbol. Define the actual Gram kernel and its unit vectors. A Schur-pair predicate records properties of supplied d,a,b; it contains no existence or chosen solution and does not assume the theorem that such a pair exists.

Use polynomial degree in WithBot N for <= bounds, and p=0 or natDegree(p)<n for strict bounds including n=0. Define fixed-bound conjugate reflection through Polynomial.reflect after mapping the actual complex starRingEnd. Define finite Fourier coefficients by all coefficient pairs, the effective ordinary polynomial by shifted integer Fourier indices, reciprocal conjugation by inverse(star z), inside roots by filtering the full root multiset, and the root product explicitly.

Use the actual full complex inner-product gradient on the actual unit Gram kernel, a real convex subset of EuclideanSpace C (Fin k). Direction combinations use arbitrary complex coefficients. Define both descent steps by a positive-half multiple of minima of positive explicit bounds; the compact complement is a concrete subset of the full unit sphere. Define affine/GMRES values by sInf/sSup of actual norm ranges and prove every required attainment separately. Define Jordan matrices, reversal, polynomial matrix evaluation, and admissibility concretely.

The following 50 independent Challenge contracts expose the whole finite route. They are specifications to be proved, not usable proof-library assumptions. No Solution may import Challenge. Dependencies below are mathematical guidance only; each Challenge declaration must state its own concrete hypotheses.

1-7: coefficient Euclidean semantics; actual Toeplitz action and algebra; nilpotent inverse; attained operator norm; exact Gram-kernel/norm-equality equivalence.
8-16: diagonal bound, scalar and dimension-one endpoints, exact Schur defect identity, strict reduction with smaller norm exactly one, active-block coordinates, reconstruction, unconditional boundary induction, and scaled full maximal-subspace formula.
17-28: bounded reflection algebra/product/evaluation and circle uniqueness; folding weights; terminating common-root reduction; finite Fourier identities/effective polynomial; reciprocal root MULTISET pairing/inside product; strict factorization; unconditional degree-preserving weighted factorization with zero/empty families and exact polynomial identity.
29-33: reflected coefficient preservation of norms and full complex forms; compression in the full maximal space; nonempty compact real-convex gradient image; every real functional's complex coefficient representation; strict directional separation.
34-40: the sole positive-half certificate; two explicit small-step bounds; exact quadratic expansion; genuine compact-complement gap; separate empty/nonempty complement estimates; unconditional descent from positivity on maximal vectors.
41-44: minimality forces full complex orthogonality; affine operator and pointwise minima exist; attained affine Toeplitz minimax, including a zero residual and an empty/dependent direction family.
45-50: Jordan reversal is an actual Euclidean isometry; lower-Jordan directions are Toeplitz; exact all-complex normalized-polynomial/residual equivalence; norm/action transport; actual GMRES infimum semantics with attained minima; complete canonical equality with polynomial/vector and all inner-minimum witnesses.

No analytic Hardy-space/compression corollary is exported: the finite subspace and coefficient route proves the complete original target without that optional layer. This is a scope choice about unused helpers, not a weakening of IE-02. Every substantial mathematical bridge on the selected route is an explicit contract; smaller implementation lemmas may later be added only after freeze.

Planned declaration names:

1. `coefficient_roundtrip`
2. `coefficient_inner_product`
3. `toeplitz_action`
4. `toeplitz_algebra`
5. `nilpotent_inverse`
6. `euclidean_norm_attainment`
7. `maximal_space_norm`
8. `schur_diagonal_bound`
9. `schur_scalar_endpoint`
10. `schur_dimension_one`
11. `schur_defect_identity`
12. `schur_strict_reduction`
13. `schur_active_block`
14. `schur_pair_step`
15. `finite_schur_boundary`
16. `scaled_maximal_factorization`
17. `reflection_algebra`
18. `reflection_product`
19. `reflection_evaluation`
20. `circle_polynomial_uniqueness`
21. `weighted_fold`
22. `common_circle_root_reduction`
23. `fourier_semantics`
24. `effective_factor_polynomial`
25. `reciprocal_root_pairing`
26. `reciprocal_inside_factor`
27. `strict_scalar_factorization`
28. `weighted_scalar_factorization`
29. `weighted_coefficient_preservation`
30. `maximal_complex_preservation`
31. `gradient_compact_convex`
32. `real_separator_complex_form`
33. `gradient_strict_separation`
34. `half_certificate`
35. `descent_step_bounds`
36. `descent_quadratic_expansion`
37. `descent_complement_gap`
38. `descent_empty_complement`
39. `descent_nonempty_complement`
40. `positive_gradient_descent`
41. `minimizer_orthogonality`
42. `affine_operator_minimum`
43. `affine_vector_minimum`
44. `affine_minimax_attained`
45. `jordan_reversal`
46. `jordan_direction_toeplitz`
47. `normalized_polynomial_residuals`
48. `jordan_polynomial_transport`
49. `gmres_extrema_semantics`
50. `canonical_jordan_minimax`
