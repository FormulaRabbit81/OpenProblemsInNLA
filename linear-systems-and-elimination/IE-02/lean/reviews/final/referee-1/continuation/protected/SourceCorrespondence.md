# IE-02 source and statement correspondence

The exact canonical source is `linear-systems-and-elimination/IE-02/README.md` at recorded commit `d348d7471e2ff881ae30fb8a9c40323a61cd383a`; the complete retained manuscript is `solution.tex`. Their original bytes, the full finite-route preflight, and the nonauthor mathematical review are bound in `SOURCE-PROVENANCE.json`. They remain external immutable packets to avoid duplication. The statement author previously read the complete manuscript and target; this draft consumes the complete new finite route and independent paper review. No fresh external-paper or public duplicate audit is claimed.

| Source obligation | Concrete definition | Proposed contracts |
|---|---|---|
| Actual Euclidean coefficient space and polynomial truncation | `H`, `coeffVector`, `vectorPolynomial`, `truncate` | `coefficient_roundtrip`, `coefficient_inner_product` |
| Lower Toeplitz algebra and finite inverse | explicit lower-diagonal `toeplitz`, `shift`, `finiteInverse` | `toeplitz_action`, `toeplitz_algebra`, `nilpotent_inverse` |
| Actual norm and full maximal singular subspace | norm of `euclideanCLM`; actual kernel `maximalSpace` | `euclidean_norm_attainment`, `maximal_space_norm` |
| Finite CF foundation proved by boundary Schur recursion | `schurM`, `schurZ`, `activeBlock`, supplied-data `SchurPair` | `schur_diagonal_bound` through `scaled_maximal_factorization` |
| Fixed degree and all-root scalar factorization | `conjReflect`, explicit Fourier coefficients, `insideRoots` as a MULTISET filter | `reflection_algebra` through `weighted_scalar_factorization` |
| Simultaneous preservation of full complex GMRES forms | actual Euclidean inner product; coefficient norm | `weighted_coefficient_preservation`, `maximal_complex_preservation` |
| Real separation of a directly convex gradient image | `gradientImage`, `separatorCoefficients` | `gradient_compact_convex`, `real_separator_complex_form`, `gradient_strict_separation` |
| Uniform norm decrease, including an empty complement | explicit `descentComplement`, `emptyStep`, `gapStep` | `half_certificate` through `positive_gradient_descent` |
| Attained affine Toeplitz minimax including zero residual | actual residual combinations; infimum/supremum of norm ranges | `minimizer_orthogonality`, both `affine_*_minimum` contracts, `affine_minimax_attained` |
| Exact upper Jordan block and all complex normalized polynomials | `jordan`, `Admissible`, `polyEval`, reversal | `jordan_reversal` through `gmres_extrema_semantics` |
| Complete original Theorem 1 | actual `worstGMRES` and `idealGMRES` | `canonical_jordan_minimax` |

The supplied-data `SchurPair` predicate merely records properties of d,a,b. Its scalar endpoint is a nontrivial witness contract, its recursive step consumes supplied smaller data, and `finite_schur_boundary` must prove existence without a CF/Schur oracle. The downstream scaled factorization and preservation contracts consume the entire resulting kernel description. It is not a typeclass or final assumption.

All degree bounds use either extended degree or an explicit zero alternative for strict bounds. The natural subtraction n-1-d is accompanied by d<n inside the Schur-pair data. Reflection preserves coefficients above its bound in Mathlib, so every product/evaluation contract has the needed degree hypotheses. Circle-root removal forces m>=1 before decreasing m. The effective Fourier degree may be zero even for nonconstant summands. Root pairing retains every multiplicity and separately excludes zero and circle roots.

The gradient coordinates are complex inner products; no replacement by real coordinates alone occurs. Real convexity is over the actual complex Euclidean coordinate space restricted to real scalars. The separator coefficients use ell(e_j)-i ell(i e_j), and descent is T-epsilon D with that sign. The compact-complement gap is proved only when the complement is nonempty; the empty branch uses its own explicit step and no invented maximum or gap.

Neither GMRES quantity nor its affine analogue is defined using an optimizer, equality, or an assumed attainment theorem. Their actual norm-range infima/suprema are linked to minima/maxima by separate unconditional finite-dimensional contracts. The final canonical theorem repeats all necessary attainment witnesses and comparison inequalities, not just a potentially totalized infimum equality. It keeps n>=2, lambda!=0, and 1<=k<n, without divisibility or eigenvalue-regime restrictions. All matrix/polynomial/vector scalars are complex.

The finite route changes proof organization relative to the manuscript: simultaneous Schur induction proves the interpolation and maximal kernel, common circle factors replace an analytic multiplicity shortcut, and fixed-degree coefficient extraction replaces circle integration. It preserves the original target exactly. The unused optional Blaschke/Hardy compression result is not a required public helper.

George Stepaniants retains mathematical authorship. The former special-case and background references retain their separate roles; this draft makes no new priority claim, external-human-peer-review claim, or formal certification claim.
