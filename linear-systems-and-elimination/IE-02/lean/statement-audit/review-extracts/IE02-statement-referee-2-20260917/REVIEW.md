# Independent IE-02 exact-statement review

**PASS — approve the mathematical meaning and scope of this exact Definitions/50-contract Challenge proposal. No statement change is requested. Actual Lean elaboration, accepted freeze, proof implementation and all runtime verification remain separate gates.**

Reviewer: `/root/mi13_statement_freeze`, 17 September 2026. Statement author: `/root/ie02_foundation_preflight`. I did not author these definitions or statements. I previously independently reviewed the finite paper route, and this report discloses and reuses that mathematical reading. The earlier paper-route approval is not counted as an exact-statement review: every concrete definition and every one of the 50 new headers has now been read and independently checked against the canonical target and route. This packet supplies one nonauthor exact-statement review. It does not certify another reviewer's work, replace the required second reviewer, or claim formal proof.

Exact reviewed identities:

| Input | SHA256 |
| --- | --- |
| Author MANIFEST.json | `972a12860c8f7c9c0374a2ad51a9eee66104c43de333b379b3dad04eb27097ed` |
| Definitions.lean | `68a516d1cde704892fecbf5cfb2e958b32fd0a7bfb3c3157a1a2ad734a525602` |
| Challenge.lean | `aac733145ff51f7abd34c52cad23f2f939cddda631c5f085e8cc1e0909877ca7` |

The complete author packet is copied under `inputs/draft`. All original bytes and the prior paper-review packet remain unchanged. No author source, canonical page, registry, problem ID, Git state, publication status or verified-target count was changed. No compiler or Git command was invoked.

## Canonical target and concrete objects

The retained canonical source is `linear-systems-and-elimination/IE-02/README.md` at recorded commit `d348d7471e2ff881ae30fb8a9c40323a61cd383a`, digest `96072d0ab9fda78de1c17ec51368b1e6f561ab0db3fa83de7231c6d6ab2c1ef0`. I reread that complete page and the complete retained solution manuscript, digest `c3bd715724ebd12f95ab75c6b63d420c2efd3132d2e600e4f4e774ee49b8e52a`. Their historical source identity is preserved; this is not a new public-HEAD or priority audit.

The final contract retains every original parameter restriction: n≥2, complex λ≠0 and 1≤k<n. The actual upper Jordan block has ones at (i,i+1). The admissible family consists of **all complex polynomials** of degree at most k with p(0)=1; vectors are complex as well. The target is equality of worst-case and ideal GMRES for that original matrix, with no doubled dimension, divisibility condition, eigenvalue phase/magnitude restriction, rank assumption, real-coefficient reduction or simple-singular-value assumption.

The 60 definitions/abbreviations are concrete. H n is the complex EuclideanSpace, rather than a raw function type carrying a supremum norm. The public operator norm is the norm of the continuous linear map obtained from the actual Euclidean matrix action. The maximal singular space is the actual kernel of A* A−‖A‖²I. Toeplitz entries, coefficient vectors, finite polynomial sums, truncated action, root multisets, gradients, perturbations and reversal are explicit. Polynomial evaluation is `Polynomial.aeval`, not a substitute chosen to satisfy the target.

`DegreeLE` uses extended polynomial degree, allowing zero without a special exception. `DegreeLT` explicitly includes zero, so the coefficient roundtrip remains correct in dimension zero. The fixed-bound conjugate reflection uses the pinned `Polynomial.reflect`; all contracts requiring degree control supply it. The finite root data are multisets, retaining multiplicities. The separator functional is real-linear on the actual complex Euclidean gradient space, and its complex coefficient sign matches the inner product's linear second slot.

GMRES and affine values are actual infima/suprema of norm ranges. None is defined through an optimizer, equality, or a promised extremum. The final contract includes inner-minimum attainment for **every** unit vector, an ideal minimizing polynomial, a worst-case unit vector, a common polynomial/vector norm-attaining witness, and the minimum/maximum comparison inequalities. Therefore the proposed equality does not exploit totalized infimum/supremum conventions to omit the printed extrema. The separate generic extrema contracts also cover n=0 and k=0 where meaningful; the canonical sphere is nonempty because n≥2.

The source manuscript's optional strict-positivity observation and unused analytic Hardy-space compression layer are not required parts of the original equality. Omitting those extra exports does not weaken the original problem or its explicit attained witnesses.

## Complete boundary review

`CONTRACT-REVIEW.json` gives a separate mathematical check and exact header hash for each numbered contract. `HEADERS.json` binds all 50 headers to the author's recorded headers and complete Comparator list. The following points summarize the main attempted failure modes; they do not replace those individual checks.

**Contracts 1–7: genuine finite semantics.** Coefficient reconstruction, Toeplitz convolution, polynomial evaluation, nilpotency and the finite inverse agree with their concrete definitions. In the empty matrix algebra identity equals zero, so the n=0 nilpotency/inverse statements are valid. Norm attainment has the needed positive-dimension premise. Kernel/norm-equality equivalence uses the positive Gram defect and remains valid at zero vectors, zero matrices and empty dimension. In coefficient_inner_product, only the first polynomial needs a degree bound: terms of the second polynomial above N cannot contribute to coefficient N. That absence of a second degree hypothesis is sound.

**Contracts 8–16: finite Schur foundation.** The scalar endpoint includes a full d=0 SchurPair, and the one-dimensional norm identity supports termination. The strict branch explicitly retains norm **equal to one** both for the transformed matrix and its active block. The append/prepend coordinate conventions select input (g,η) and output (0,Vg); contraction forces η=0 in the equality case. Both inverse equations and the entire maximal-space pullback appear, not merely one inclusion or an operator bound.

`SchurPair` is a predicate recording the properties of supplied d,a,b. It includes d<n, exact numerator degree d, denominator degree at most d, b(0)=1, coprimeness, nonvanishing on the closed disk, disk domination, circle modulus equality, actual interpolation, the complete kernel formula, its action and exact dimension n−d. Its smaller-pair premise appears only in the induction-step contract. The separate `finite_schur_boundary` contract must prove existence from positive dimension, Toeplitz structure and norm one alone. No Schur/CF or maximal-space oracle reaches the final theorem.

The recursive numerator c b+X a has exact degree d+1, since c b cannot cancel the degree-d+1 term of X a. Strict |c|<1 makes the reconstruction and coprimeness argument valid. The provided inverse identifies B uniquely, so an additional Toeplitz assumption on B is not required in the pair-step statement. Natural subtraction n−1−d is controlled by d<n. Scaling by the nonzero matrix's positive actual norm supplies the original-scale kernel and action. Zero T is excluded only where division is needed, not in the affine conclusion.

**Contracts 17–28: all weighted factorization cases.** Reflection uses explicit degree bounds, and evaluation at reciprocal conjugation has its nonzero-input hypothesis. The unit circle is required as an infinite set, not a finite grid. Weight folding permits zero weights. Common-circle-root reduction contains the nonzero-family hypothesis that forces m≥1 before decreasing m. It therefore handles repeated circle factors by genuine degree induction rather than presuming even multiplicity.

The effective Fourier degree can be zero even when individual summands are nonconstant. The effective polynomial explicitly has degree 2ℓ and nonzero constant coefficient, is self-conjugate-reflective, and has no circle root. Reciprocal pairing and the inside factor keep full root multiplicities and separately exclude zero roots. The inside-factor scalar is only claimed nonzero for a generic reciprocal polynomial; its required positive real normalization is derived later from the sum-of-squares circle identity. The final weighted factorization is unconditional for arbitrary finite families and nonnegative real weights, with no sum-to-one requirement. Empty families, all-zero data, constants, zero weights and repeated roots are retained, as is the exact polynomial identity needed downstream.

**Contracts 29–33: full complex preservation and separation.** The coefficient-preservation identity is complex, not only an equality of real parts. It needs no nonnegative-weight hypothesis because its supplied polynomial identity already implies the linear coefficient identities. Arbitrary Toeplitz symbols need no degree bound: coefficient extraction automatically discards terms too high to contribute. The maximal-space compression preserves norm and every complex form simultaneously, giving real convexity of the gradient image itself. Nonemptiness and compactness are explicit obligations. Repeated maximal values and empty direction families are allowed.

For a real functional ℓ, the coefficient ℓ(e_j)−iℓ(i e_j) satisfies

    ℓ(z) = Re Σ_j (ℓ(e_j)−iℓ(i e_j)) z_j.

This sign is correct, and linearity of the second inner-product argument then gives the direction D=Σ c_j R_j with positive descent form. No complex-linear separation theorem is silently substituted for real separation.

**Contracts 34–40: actual uniform descent.** The sole planned numerical certificate is the exact real inequality 0<1/2. Both concrete step definitions use this positive factor. Its kernel LeanCert execution, minimal adequate settings and actual source-level downstream consumption remain future proof-review obligations; no certificate has run.

The complement is exactly the closed unit-sphere set q(x)≤γ/2. A positive gap is claimed only when that set is nonempty; norm attainment and positivity on maximal vectors supply the contradiction at any putative full-norm point. The empty case has its own step and never invents a maximum or gap.

In the nonempty descent contract, a separate maximal-space positivity premise is correctly absent. Outside its concrete complement, q(x)>γ/2 holds by definition. There the expansion gives a uniform bound at most t²−εγ/2. On the complement, the supplied β-gap and |q(x)|≤t‖D‖ give at most t²−β+εC≤t²−β/2, where C=2t‖D‖+‖D‖². The explicit step satisfies ε≤1 and both required positive upper bounds. Thus the statements control the full sphere uniformly, including the empty-complement branch, and actual norm attainment yields strict operator descent. No differentiability or simplicity premise is used.

**Contracts 41–50: attainment and original transport.** Minimality on the complex affine direction space contradicts the negative εD perturbation if zero is absent from the gradient image, giving all complex orthogonality equations in one maximal unit vector. The separate operator and vector minima exist because finite-dimensional linear images are closed; coefficient dependence does not require coercivity in coefficient space or an injective parameterization. Both statements permit empty direction lists and zero vectors/matrices.

The attained affine theorem allows a zero minimizing residual and includes every inner minimum. Its positive-dimension premise supplies a unit vector in that branch. Otherwise the already proved complex orthogonality gives the Pythagorean lower bound at the common witness. Reversal is the actual unitary permutation taking the original upper Jordan block to the lower block; the lower-Jordan powers are Toeplitz. The two-way normalized-polynomial/residual statement retains all complex coefficients and powers 1 through k. Polynomial action, norm and sphere transport are explicit, so the final equality and extrema concern the original upper Jordan block.

I found no mathematical counterexample, unexplained strengthening, canonical scope loss, illicit premise, vacuous final target, or hidden foundation assumption in these exact proposed statements. The substantial new finite Schur, weighted-factorization, coefficient-preservation, separation/descent and minimax foundations remain obligations to implement internally. Mathematical statement approval is not evidence that those proofs already exist in the pinned library or will be easy to implement.

## Pins, evidence and execution boundary

All 23 author manifest entries and the exact draft inventory were rehashed. The audit checked 16 external provenance bindings, all 22 listed Mathlib source bytes, the retained LeanCert source and pinned review/checker guidance. The earlier 51-file paper-review packet was reauthenticated and remains a separate paper-only review. All ten campaign package revision pins agree. Lean remains v4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`.

Relevant actual primary semantics were inspected in this and earlier source reviews, including Euclidean matrix action, adjoint, fixed-bound reflection, finite roots, separation and finite-dimensional attainment. For this exact interface, the `Fin.cons`/`Fin.snoc` definitions and `Polynomial.aeval` definition were read directly; the reflection coefficient behavior was rechecked. These are scoped source reads, not a full audit of transitive Mathlib proofs. No fresh external-paper search or global duplicate search was performed; historical searches remain historical, as the draft honestly states.

The recorded numerical-first plan's target/definition-plan hashes match the current bytes and its recorded timestamp precedes the draft seal. I did not witness the original file-creation event and make no stronger forensic chronology claim. The exact one-half target and intended descent consumer agree with that plan.

The author's inspected read-only Python validator was actually run and passed: 50 headers, complete Comparator coverage, 50 deliberate specification holes, zero definition holes, source bindings, dependency pins and the v0.4 metadata schema. The independent reviewer helper then passed **283 metadata/header/hash checks**, with **74 external bindings**. It also indexed **60 concrete definitions/abbreviations**. The full original draft was unchanged before/after. One initial reviewer-helper attempt treated the previous paper manifest's file list as a mapping; adapting the reader to its actual list schema fixed this tooling error. It was not a Lean failure and changed no source.

The deliberate Challenge holes are specifications, not proved theorems. There is no Solution and no accepted statement freeze. The Comparator configuration covers exactly all 50 names and permits only the three foundational axioms, but Comparator has not been executed for this review. No Lean parsing/elaboration, proof execution, kernel LeanCert run, kernel check, sandbox/isolation check, negative control or GitHub run is claimed. Static validation cannot establish that the current declarations elaborate.

After both required nonauthor statement reviews, root still owns actual local elaboration of these exact bytes, with at most one compiler process, one thread and 4096 MiB. Any mathematical boundary change returns to the statement reviewers. Root acceptance of the actual elaboration precedes immutable freeze and proof implementation. The eventual full proof reviews and real non-root Linux GitHub Comparator/kernel/sandbox checks remain mandatory and distinct from local development.

## Review guidance and attribution

Pinned Tau Ceti REVIEWING and the correctness, generality, proof-quality, reuse and attribution rubrics at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b` were applied manually. Comparator guidance is pinned at `2312244ac716564a61cc0bf4e107d9abf1757a61`. This is a scoped agent review, not official Tau Ceti output or external human peer review. Correctness/general scope pass for the statement proposal. Future proof quality and runtime soundness have no approval here because implementations do not yet exist.

George Stepaniants retains mathematical authorship and receives the Department of Computing and Mathematical Sciences, California Institute of Technology attribution without email. The Tichý–Liesen–Faber problem and special cases, Faber–Liesen–Tichý approximation background, Courtney–Sarason interpolation background, and existing library/code authorship remain distinct and retained. No publication, permanent-ID change or completed-original-target count increment is authorized or claimed by this review.
