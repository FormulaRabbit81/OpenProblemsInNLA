# NR-04 / PF-05 / SP-15 feasibility decision

**Select SP-15 for independent statement preparation.** The original existence argument can be specialized to an exact rational base point with an invertible 9×9 derivative minor, allowing use of the existing inverse-function theorem. This is a feasible full-target route; it is not a Lean proof, an approved statement freeze, or a solved-count increment.

I read the exact canonical pages at retained local upstream/main commit `d348d7471e2ff881ae30fb8a9c40323a61cd383a`, the complete NR-04 and PF-05 supplied manuscripts, and the complete SP-15 Markdown and TeX. Sources, Git blobs and hashes are retained. The retrieved review/provenance dossiers are not misrepresented as freshly rerun or fully audited mathematical sources. I performed only read-only Git retrieval, library inspection and a small exact Python preflight; no Lean compiler, cache mutation, network request, Git mutation or push occurred.

## Why SP-15 is now bounded

The supplied proof does not give a numerical point on a fiber: it selects a point of maximum differential rank and invokes constant rank. I did not assume that implicit existence was an explicit witness. Instead I first wrote the numerical preflight, then checked the actual coefficient map at `(1,2,3,4,4,4,1,1,1,1)`. The 9×10 Jacobian has rank nine; the first nine columns have determinant **−1088**. The positive-definite Q has exact leading principal minors **4,15,50**. A second compact expansion of the coefficient determinant was checked against the direct 3×3 expansion.

The standard-library exact integer-polynomial/Fraction script and its actual run receipt, output, source hashes and a triangular factorization certificate are retained. Default Python had no SymPy; no dependency installation was attempted. The first standalone check is retained under history. These are preflight computations, not kernel verification or independent review. Every finite identity must be re-proved from the concrete definitions in Lean.

The full route is eight bounded implementation areas after statements are accepted:

1. Concrete ten-parameter P,Q,A definitions, genuine matrix square roots, finite-index reindexing and actual singular-value definitions.
2. Kernel LeanCert scalar box bounds, positive definiteness throughout the explicit 1/16 box, and disjoint p intervals.
3. The actual 3×3 determinant coefficient identity and its nine real polynomial coordinates.
4. Formal derivative of those coordinates at the rational point, plus exact 9×9 LU reconstruction and triangular nonsingularity. This avoids a factorial determinant computation.
5. The augmented map G=(Φ,d), invertible strict derivative, and a local inverse restricted to the box. Its d coordinate proves injectivity of the local curve.
6. The full shifted Gram determinant identity for every complex shift, polynomial identity and all ordered singular values with multiplicities.
7. The block-flag unitary-intertwiner argument and positive-phase normalization; the box removes the need for an eigenvalue-permutation classification.
8. Arbitrarily many distinct parameters in the one-dimensional local fiber, yielding the exact N=9 negation of the original question.

These are new proof obligations, not claims that imports already solve the problem. The block-flag argument and determinant-to-singular-value bridge remain substantial, but their necessary ingredients are ordinary finite-dimensional matrix algebra and already present spectral/analytic APIs. I found no unresolved external theorem comparable to the Frenkel identity in MI-27.

## Genuine reusable primary APIs

Pinned Mathlib remains `0df444a360eaa60ab8c11dca51a86af692955474`.

- `HasStrictFDerivAt.toOpenPartialHomeomorph`, `eventually_right_inverse`, and `localInverse_continuousAt` in `Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean` supply an actual local inverse at an invertible strict derivative. I read their hypotheses and proofs. `Implicit.lean` also supplies a genuine implicit function API, but the augmented equal-dimension map is simpler here.
- `Matrix.det_fromBlocks₁₁` and `det_one_add_mul_comm` supply the actual Schur/Weinstein–Aronszajn identities. The proof must discharge their invertibility hypotheses; these cannot be assumed from symbolic cancellation.
- `CFC` positive square-root results, `IsStrictlyPositive.sqrt`, and `Matrix.isStrictlyPositive_iff_posDef` supply the actual square roots and invertibility. The proof needs only these algebraic properties, not square-root smoothness.
- `eigenvalue_mem_ball` and `Matrix.IsHermitian.posDef_iff_eigenvalues_pos` prove positive definiteness from the explicit diagonal bounds. There is no need to compute symbolic eigenvalues of the varying Q.
- The accepted MI-13 public `gram_charpoly`, actual singular-value definitions and sorted Gram eigenvalue argument provide genuine reusable semantics. They preserve multiplicity and zeros. The full MI-13 SVD development need not be copied into this project just to name it as reuse; select the smallest actual source dependency closure or use the same underlying pinned APIs with attribution.

`LIBRARY-BINDINGS.json` records the bytes. `NUMERICAL-OBLIGATIONS.md` fixes the point, box, coefficient order, minor, LU convention and full quantified endpoints before Lean implementation.

## The two rejected alternatives

**NR-04:** the seven-term integer upper certificate is easy, but it proves only the known upper bound. The original question requires ruling out every real nonnegative 9×6 by 6×9 factorization. The supplied lower bound needs the polygon contact lemma, normalization to a polytope section, and the three-dimensional bound of at most eight facets for six vertices, before Sylvester's rank inequality. The pinned searches did not locate the required polygon/Euler/polyhedral facet pipeline. A finite check of the upper certificate is not the full problem.

**PF-05:** size two does not make this a single fixed counterexample. It is an equivalence for every rank-three matrix and all factor families, including zeros. The source's zero-pair construction is explicit, but the positive-entry case invokes Dawson–Hoşten–Kubjas–Metsälampi Theorem 5.2 without proving it. Its integration lemma and congruence normalization also need formal development. Proving only the zero-entry construction, assuming the positive-entry theorem, or verifying a 2×2 determinant identity would leave the original universal target unfinished.

## Duplicate and verification scope

A new scan of every retained complete tree JSON checked all **210 immutable trees, 256 heads, 14 public repositories** for NR-04/NR04, PF-05/PF05 and SP-15/SP15 Lean/formalization paths. No target-named path was found. This is not a fresh network sweep, a private/deleted-head claim or a search for arbitrary unnamed content.

Two independent nonauthor statement reviews, actual elaboration and coordinator freeze must precede implementation. The current preflight author cannot be counted as a nonauthor reviewer of these new numerical statements. Later source acceptance, actual local Lean results, final GitHub non-root Comparator checks, metadata and upstream PR remain separate gates. No theorem has been added or counted by this feasibility task.
