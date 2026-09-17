# Definition and exact contract plan — before Lean statement code

Statement author: /root/mi13_full_referee2, with substantial OpenAI Codex assistance. This author is ineligible as a nonauthor statement reviewer. Attribution: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology; Fortier Bourque and Ransford retain the original question and generic-finiteness attribution. No email is included.

The literal target is the negation of the canonical universal finite-bound statement. The proof produces arbitrarily large finite families in dimension nine, with every ordered singular value equal for every complex scalar shift and no pair related by any U with UᴴU=I. No precondition named after the desired theorem, assumed coefficient fiber, oracle, external theorem axiom, chosen favorable eigenvalue ordering, or sampled set of shifts is admitted.

Definitions contain data and actual established Mathlib operations only: finite coordinate functions, the exact open box, P,Q, the genuine CFC square roots, nested block matrices and finite reindexing, the determinant polynomial evaluated at complex u,s, nine explicit real coefficient polynomials, the augmented coefficient map, literal J/L/U data, and actual matrix/singular-value predicates. No sorried definitions, new axioms, theorem witnesses, or proof-bearing implementation files are allowed.

The derivative contracts use the actual strict Fréchet derivative and Matrix.mulVecLin.toContinuousLinearMap. The invertible-equivalence contract must match the exact augmented numerical derivative. The local inverse is an existential conclusion proved using Mathlib's existing inverse-function theorem; it is not a field of an assumed structure. Its continuity and right-inverse neighborhood allow a local fiber with freely prescribed d.

The two major transports remain separate unconditional goals: equal coefficients imply shifted Gram characteristic-polynomial equality and every ordered singular value; arbitrary unitary similarity of constructed matrices implies parameter equality by the actual kernel flag. The last theorem expands the exact canonical statement, rather than counting a conditional reduction.

## Exact contract list and purpose

1. `box_scalar_certificate` — Kernel-mode LeanCert rational box bounds, including the 3/4 dominance margin, genuinely consumed in box geometry and positivity.
2. `parameter_box_geometry` — The actual open box is open and contains the fixed rational base point.
3. `parameter_box_bounds` — Positive p coordinates and positive a,b, plus strict Q diagonal dominance with margin 3/4 throughout the box.
4. `p_intervals_separate` — Different p-coordinate intervals are disjoint even for two different points of the box.
5. `parameter_matrices_positive` — Actual Matrix.PosDef for both parameter matrices throughout the box.
6. `square_root_semantics` — Actual CFC square-root Hermitian/square/invertibility facts, no assumed root matrices.
7. `coefficient_determinant_identity` — For every real parameter and all complex u,s, the actual 3×3 determinant equals u³ plus the nine real coefficients times their fixed monomials.
8. `coefficient_base_value` — The exact nine coefficient values at the fixed base point.
9. `coefficient_strict_derivative` — The actual strict derivative of the concrete coefficient map at the base point is the literal 9×10 Jacobian.
10. `jacobian_lu_certificate` — The literal first-nine-column minor equals L U; L is unit lower triangular, U upper triangular, and the product of U diagonal entries is −1088.
11. `jacobian_minor_nonsingular` — The actual determinant of that minor is −1088, hence nonzero, using triangular factorization rather than permutation expansion.
12. `augmented_strict_derivative` — The actual augmented coefficient map has the explicit 10×10 strict derivative.
13. `augmented_derivative_equivalence` — The actual augmented derivative is represented by a continuous linear equivalence; no derivative-invertibility assumption.
14. `local_augmented_inverse` — Existence of a genuine continuous-at-base local right inverse, mapping a neighborhood back into the explicit box.
15. `local_coefficient_fiber` — An unconditional nonempty local coefficient fiber parametrized by d, with the actual coefficient map constant.
16. `regularized_gram_blocks` — The regularized shifted Gram matrix is exactly the explicit three-block matrix for every complex shift and every real t.
17. `schur_positive_blocks` — The actual two Schur pivot blocks are positive definite for every complex shift and positive t.
18. `shifted_gram_determinant` — The exact shifted Gram determinant identity for every complex shift and t>0; no commutativity premise.
19. `equal_coefficients_gram_charpoly` — Equal concrete coefficients imply equal actual Gram characteristic polynomials for every complex shift.
20. `gram_charpoly_singular_values` — For arbitrary finite square complex matrices, equal Gram characteristic polynomials imply equal actual singular values at every natural index, with multiplicities and zeros.
21. `equal_coefficients_shifted_singular_values` — Equal coefficients yield the literal all-complex-shift singular-value relation of the original question.
22. `constructed_kernel_flag` — The actual kernels of the constructed block matrix and its square equal the fixed coordinate flag.
23. `unitary_intertwiner_blocks` — Every original one-sided-unitary intertwiner is a three-block diagonal unitary and intertwines the two nonzero blocks.
24. `middle_block_conjugacy` — The middle block of any such intertwiner simultaneously conjugates the actual P,Q matrices.
25. `parameter_slice_rigidity` — On the box, every simultaneous unitary conjugacy of P,Q forces all ten parameters to agree.
26. `constructed_unitary_injectivity` — Unitary similarity of constructed matrices forces parameter equality.
27. `finite_fiber_selection` — For every M choose M+1 distinct box parameters with all nine actual coefficients equal.
28. `arbitrary_finite_counterfamilies` — For every M construct the complete finite complex 9×9 counterfamily, with every shift and every singular index and no unitary-similar pair.
29. `canonical_finiteness_false` — Negation of the literal canonical universal finite-bound statement, including n≥1, M≥1 and i<j.

## Gates and permitted work

Challenge will contain exactly these intentional specification holes, imported only from concrete Definitions. No Solution file exists at this stage and no solution may import Challenge. The final Comparator theorem list must equal this list, with no definition holes and only propext, Quot.sound, Classical.choice permitted. Draft status must not be changed until two independent nonauthor statement reviews, actual serial local elaboration, and a coordinator freeze.

Reuse Mathlib's existing CFC.sqrt, strict-derivative inverse-function theorem, Schur-complement determinant identities, Gershgorin and Hermitian positivity, and ordered Gram eigenspace APIs. The accepted MI-13 singular semantics are a byte-bound reuse reference; avoid copying its unrelated commutator/SVD development. If an exact existing lemma replaces a planned implementation helper, use it instead. The 9×9 determinant must use the exact LU certificate, not 9! expansion. All numeric Jacobian entries must be derived from the actual coefficient functions before they can be used to obtain an inverse.
