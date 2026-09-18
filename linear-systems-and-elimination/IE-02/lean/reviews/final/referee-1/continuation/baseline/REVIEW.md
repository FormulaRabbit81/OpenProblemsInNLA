# IE-02 independent full proof review, original local121 sources

**Verdict: REQUEST_CHANGES_REUSE_ONLY.** I found no mathematical or statement-fidelity gap in the complete 56-module implementation of the 50 frozen contracts. One private matrix-action helper duplicates an existing public project theorem and should use it directly. This is a source-quality correction, not a counterexample or a weakened mathematical claim. Approval of corrected bytes requires a separate continuation with successful source-matched local evidence.

Reviewer: `/root/mi13_full_referee2`, 17 September 2026. I authored SP-15, not IE-02. The IE-02 authors were the coordinator and the other implementation agents. I previously reviewed the Reflection fragment; that bounded review is not substituted for this full review. I have not edited any IE-02 source, run Lean or Lake, invoked Git or Comparator, or used the network during this review. The Python scripts here authenticate existing evidence; they are not mathematical proof checkers. No official Tau Ceti service or human peer-review endorsement is claimed.

## Bound source and scope

The canonical target is `linear-systems-and-elimination/IE-02/README.md`, retained at the recorded repository commit `d348d7471e2ff881ae30fb8a9c40323a61cd383a`. Its snapshot SHA-256 is `96072d0ab9fda78de1c17ec51368b1e6f561ab0db3fa83de7231c6d6ab2c1ef0`. I read the full canonical page and supplied 15028-byte manuscript, SHA-256 `c3bd715724ebd12f95ab75c6b63d420c2efd3132d2e600e4f4e774ee49b8e52a`, including its stronger affine Toeplitz theorem and its original mathematical references. I then read all 56 current module sources in full, the complete concrete Definitions, all 50 Challenge contracts, and the numerical-first and correspondence records.

The review is bound to the source hashes in `STATIC-COVERAGE-AUDIT.json` and the immutable copies under `snapshots/project`. The 13 protected files still match their frozen hashes. Each of the 50 public theorem headers occurs verbatim and exactly once in a module reachable from Solution. The entire project-owned closure consists of the 56 reviewed sources, with no Challenge import or undeclared project import. `Solution.lean` contains only imports and trust reporting/assertions; the byte-identical local filename `IE02Solution.lean` introduces no renamed mathematical declaration.

The original local report is SHA-256 `b21664f7c95422443f409dea6ac42bd69195574ffd27d7ea142219f8ef652ddc`. Its final local121 receipt is SHA-256 `c5ee2e77958e5b2f14b9fd27324323d35a8925a020e576318f469d2c70131be2`. This review does not approve later source changes automatically.

## Pinned rubric decisions

I applied the five retained rubrics and REVIEWING.md from `TauCetiProject/TauCetiReview` at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`. Their exact hashes are retained in STANDARD-BINDINGS and the packet snapshots.

| Rubric | Decision | Reason |
| --- | --- | --- |
| Correctness | Approve within this full source-review scope | The original complex Jordan/GMRES theorem and all attainment clauses are proved from concrete objects; the analytic and algebraic foundations are supplied internally. |
| Generality | Approve | Original dimensions, nonzero complex shift, polynomial degree range and full complex quantifiers are retained. Helper theorems often prove stronger ranges and explicitly cover degeneracies. |
| Proof quality | Approve apart from R1 under reuse | The decomposition follows the mathematics, explains delicate definitional changes, and uses named algebraic/analytic APIs. Frozen aggregate contracts and redundant frozen hypotheses are retained deliberately. |
| Reuse | Request changes / block original approval | R1 is an exact duplicate of a public helper already in the same final import closure. The replacement is concrete and acyclic. |
| Attribution | Approve source contribution scope | George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, is credited; original mathematical and library attribution and AI assistance are disclosed. No email appears in the scanned active sources or contributor metadata. |

The user's frozen-contract, standalone-project scope matters: I am not requesting renaming, dropping original hypotheses, or refactoring unrelated library code to obtain an abstract library API. In particular, the explicitly unused original shift/degree hypotheses are not grounds for weakening the frozen original target or creating fake uses.

## Required source correction R1

At `NLA/IE02/JordanTransport.lean:29`, private `euclidean_mul_apply` has the same statement and proof as public `NLA.IE02.euclideanLin_mul_apply` at `NLA/IE02/SchurEnergy.lean:25`. Both expose the same exponent-two matrix linear maps, rewrite `Matrix.toLpLin_mul_same`, and close by reflexivity. JordanTransport uses its private duplicate once, at line 78.

Import `NLA.IE02.SchurEnergy`, delete the private duplicate, and replace that single use with `euclideanLin_mul_apply`. SchurEnergy imports SchurDefect and Definitions, so this does not create a cycle. Keep all frozen statements and definitions unchanged. Preserve the original local121 evidence and run the affected closure locally on the corrected bytes before closing this finding. The existing proof is mathematically correct; the requested correction complies with the pinned rubric's direct-reuse requirement and reduces duplicated maintenance.

Actual read-only searches are recorded in `REUSE-SEARCH.json` with commands, raw output and hashes. They searched pinned Mathlib polynomial, normed-space, topology and relevant full-tree theorem names, and the complete current project helpers. The searches located already-used polynomial reflection/degree/root-factor APIs, compactness/nearest-point and separation APIs, and R1. They did not locate a complete direct finite Schur, weighted scalar factorization or GMRES theorem that supersedes the present foundations. This is a bounded API-search result, not an exhaustive literature claim. Only pinned TauCetiReview guidance was available locally; no full pinned Tau Ceti mathematical source checkout was present in the searched locations, as the coordinator also confirmed. I do not claim to have searched absent mathematical code.

## Mathematical review

### Concrete semantics and original target

`H n` is the complex Euclidean space on `Fin n`; it is not the supremum norm on a bare function space. Matrix action uses Mathlib's exponent-two Euclidean linear map, and `operatorNorm` is the norm of its actual continuous linear map. `maximalSpace` is the kernel of the actual Gram defect. The polynomial residual is genuine polynomial evaluation in matrices; admissibility means degree at most k and value 1 at zero, with arbitrary complex coefficients. The upper Jordan shift has the intended superdiagonal orientation.

The final theorem retains n at least two, nonzero complex lam, and 1 ≤ k < n. The two GMRES quantities are actual infimum/supremum value-set definitions. The proof also supplies minimizing polynomials, maximizing unit vectors, common optimal witnesses and attainment for every inner minimum. Thus the conclusion is not obtained through totalized-infimum behavior on an empty or unbounded set. The affine theorem is stronger than needed, which explains several unused frozen original hypotheses.

### Coefficient, Toeplitz and maximal-space foundations

Coefficient roundtrip uses the existing finite polynomial construction, with an explicit zero-polynomial alternative in `DegreeLT` to handle dimension zero. Toeplitz action really is truncated polynomial multiplication. Its algebra map is proved before nilpotence and polynomial evaluation are used. The inverse of a scalar identity plus nilpotent matrix is a finite geometric sum, with both multiplication orders justified.

Norm attainment uses the compact unit sphere in the actual Euclidean space for positive dimension. Maximal-space equivalence uses the self-adjoint Gram operator and Mathlib's Rayleigh stationary-point result, with zero-vector and nonzero-vector cases separated before division. It does not assume a simple maximal singular value or select just one eigenvector as a replacement for the whole maximal subspace.

### Complete finite Schur argument

I checked all eleven clauses of the Schur-pair boundary, not only its displayed norm estimate. At the scalar endpoint, norm exhaustion forces the visible higher coefficients to vanish; the proof does not incorrectly identify an arbitrary full polynomial from its finite Toeplitz truncation. The strict step writes the relevant matrix as a positive scalar identity plus a nilpotent matrix, proves its two-sided inverse, and derives the genuine defect energy identity. Norm one for the transformed contraction follows using a transformed norm-attaining vector and invertibility.

The active block has the correct dropped-last-input/added-first-zero-output coordinates. The off-block first coordinate is forced to zero by equality in the contraction bound. The polynomial recursion has the stated degree bounds, b(0)=1, coprimality and disk denominator nonvanishing, including c=0. Its transfer identifies the actual supplied finite Schur matrix by inverse uniqueness. The kernel pullback is established in both directions, and the dimension statement is transported by the explicit prefix/append linear equivalence. Strong induction lowers dimension and handles dimension one. No Carathéodory–Fejér or Schur theorem is assumed as an oracle. Positive-norm scaling excludes the zero matrix before normalization.

### Weighted factorization and full complex preservation

Fixed-degree reflection retains degree slack and satisfies the correct conjugate-reciprocal evaluation identity. Fourier data are finite double sums of coefficients, with exact identities at every unit-circle point. The effective-degree construction includes ell=0 and proves both the leading and constant coefficient nonzero before invoking root factorization. Root pairing is a multiset identity, so repeated roots retain multiplicity. Inside/outside filtering excludes zeros and unit-circle roots before reciprocal division; an empty root multiset is allowed.

Strict scalar factorization derives its real positive normalization from an actual positive circle value. General weighted factorization treats the all-zero case and removes a common unit-circle factor by degree induction. The factor is never canceled at its zero. Nonnegative weights are incorporated by their real square roots. The resulting identities hold on the whole unit circle and are converted to polynomial identities using its infinitude. No finite numerical sampling, unproved even-multiplicity assertion, numerical root isolation or positivity oracle enters this reasoning.

The coefficient-preservation theorem preserves the full complex pairings for arbitrary Toeplitz directions. Real parts are taken only for the appropriate norm/gradient statements. Its maximal-space application produces a single unit vector in the actual maximal kernel realizing the weighted complex data, not merely a point in a convex hull or a vector in a larger substitute space.

### Convexity, separation and uniform descent

The gradient image is nonempty compact and convex over the reals; convexity comes from the scalar-factorization preservation theorem. The real functional is represented with the correct complex coefficients, respecting that the complex inner product is linear in its second slot. The orientation of the pinned Hahn–Banach separation theorem gives a strictly positive margin away from zero, as used in the direction construction.

The positive-half LeanCert certificate is consumed by `half_min_bounds`, and that result proves positivity and upper bounds for both actual descent-step choices. The norm expansion is symbolic. The complementary compact set is treated separately when empty and when nonempty; a positive norm gap is extracted only in the latter case. The fixed step combines the positive-gradient and norm-gap bounds uniformly. Pointwise strict decrease is converted to strict operator-norm decrease at an actual norm-attaining vector of the perturbed operator. No input-dependent step is substituted for the required common step. A minimizing coefficient tuple then rules out the separator and gives full complex orthogonality.

### Affine minima and canonical transport

Affine minima follow from nearest-point existence in a closed finite-dimensional range, which covers dependent or empty lists of directions. Zero optimal residual is handled with an explicit unit vector. In the nonzero case, maximal-space orthogonality and the squared-norm identity give a common vector/polynomial saddle witness. The actual infima and supremum are identified by least/greatest witnesses, and inner minima are attained.

Polynomial coefficient parametrization is proved in both directions for all admissible complex polynomials, before any infimum is transported. Reversal is the genuine coordinate permutation, is involutive and norm preserving, and conjugates the upper Jordan matrix to the lower Toeplitz form. Polynomial intertwining preserves multiplication order. Equality of vector and operator value sets is established before taking extrema. This completes the original upper-Jordan question with its full quantifier ranges and all requested attainment clauses.

## Computation, trust and evidence

The only new numerical certificate is `(0 : ℝ) < 1 / 2`, executed by explicit `interval_decide (trust := kernel)`. I verified its actual consumer in the descent proof. Everything parameter-dependent is symbolic; there is no interval subdivision, determinant enumeration or sampled substitute for a universal identity. The sources add no heartbeat, recursion, memory or lint-suppression overrides. Their small module decomposition permits exact successful outputs to be reused during development.

I authenticated all 56 current source hashes, all 33 distinct successful-origin receipts, full relevant raw logs and existing output hashes. Every recorded module invocation has `--threads=1 --memory=4096`; the receipts bind one compiler process. The actual compiler binary hash matches the receipts. Each dependency output hash matches the corresponding exact successful source origin. The local121 aggregate reports exactly the ordered 50 Comparator theorem names, each with only `propext`, `Classical.choice`, and `Quot.sound`; its kernel trust assertions passed. These are existing local executions, not fresh executions by this referee. The packet stores the receipts and logs so their source linkage can be checked independently.

There are **11 actual unused-variable warning diagnostics** in the successful original closure, all in frozen public contracts: Coefficients hp; Reflection hq; CommonCircleRoot hz; DescentGap hn/hne; DescentConclusions hne/hne/hK; CanonicalJordan hlam/hk/hkn. They are not compilation failures and are not silently suppressed. Counting the log's explanatory phrase “silence this warning” as another warning would be incorrect; the audit now counts anchored diagnostic lines.

The source scan found no active `sorry`, `admit`, custom axiom, native/unsafe proof shortcut, custom elaborator injection, Challenge import or resource override in the 56-module closure. That scan supplements the source review and measured axiom reports; it is not a standalone soundness proof. I read the pinned LeanCert verification-mode dispatch and trust classification: explicit kernel mode does not fall back to native verification, and the trust assertion rejects custom or sorry axioms. Twenty-two previously bound Mathlib source files were rehashed; additional relevant separation, Rayleigh, nearest-point and LeanCert verification source bytes are also retained. Selected APIs were inspected, not the entire transitive dependency implementation.

## Remaining gates and limits

The current README, STATE, contract status, Lake registration and formalization.yaml still describe the deliberately retained statement/preparation stage. Their publication update is a separate recorded continuation, not part of this mathematical source approval. It must register the real Solution target, reflect the actual review/check status and retain historical records without rewriting them. The canonical page, indexes, affiliation presentation and any PDF rendering are likewise later publication checks.

The real clean, non-root Linux Comparator/default-kernel/sandbox/rejection run is **not yet performed for this IE-02 final source set**. This review makes no success claim for it, GitHub, a published commit, a second referee, or a whole-problem count increment. The concrete next gate is R1's small source correction and authenticated local rerun. After that, a separate continuation can approve the corrected full source set, followed by the other independent review and the prescribed publication/runtime workflow.
