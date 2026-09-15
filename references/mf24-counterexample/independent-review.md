# MF-24: independent informal mathematical review

**Review date:** 15 September 2026 (UTC).  
**Reviewer:** Codex AI assistant, in response to the submitter's request for verification.  
**Verdict:** PASS for the complete negative answer to MF-24's dimension-independent boundedness target. No mathematical correction to the supplied proof is required by this review.

This reviewer did not write the supplied manuscript or its original verification scripts. The review consists of a direct analytic audit, new independently written computations, and inspection of all four rendered PDF pages. It is one AI-agent informal review, not external human peer review or Lean/formal verification. It does not authenticate the manuscript's authorship or establish publication priority.

## Materials and exact target

The reviewed manuscript is *Unbounded polynomial norm ratios for super-identical pseudospectra*, supplied as `MF24_counterexample_clean.pdf` and archived for submission as `proof.pdf`. Its SHA-256 is:

```text
1ae9316d7c935f6133a54b133d36bc55dce34f3a252b44c314b3b45a54514139
```

This exactly matches the `proof.pdf` hash in the supplied `verification.txt`. The submitter subsequently supplied the complete MF24_PR folder, including all seven other files named in that log. All 23 checksums in its SHA256SUMS manifest matched. The construction and both main checking scripts were read and rerun successfully with the pinned NumPy 2.3.5 and SymPy 1.14.0 (Python 3.14.6 in this review). Their fresh output is retained as `original-exact-rerun.txt` and `original-numeric-rerun.txt`. The reviewer's separately written checker is named `independent_check.py`; its output is `independent-results.json`. The original development and stress-test logs are retained as historical records; only explicitly listed reruns are claimed here.

The canonical target was reviewed at upstream/local commit `6d840cd6bdf811e166ba0a07501407fb121ff0ce`, in `matrix-functions-and-stability/MF-24/README.md`. The public main-branch page viewed on the review date agreed with that target and retained Partially resolved status. The question asks whether the spectral-norm polynomial comparison constant can be bounded independently of dimension, for pairs whose complete singular-value lists agree after every complex shift. Dimension-dependent polynomials are permitted. The canonical page explicitly identifies uniform boundedness as its admission target and keeps sharp constants as a related question.

## Analytic audit

### 1. Construction and quantifiers: PASS

For each integer m >= 2 and real t > 1, the words have exactly (m+1)^2-1 positive weights and define nonnegative, strictly upper-triangular, nilpotent matrices of order N=(m+1)^2. The bridge placements in equation (5) match the transfer-product order used on page 2. The polynomial has degree m(m+2)=N-1, so its highest term is present. Real matrices and real polynomial coefficients are admissible special cases of the complex target.

### 2. Equality after every complex shift: PASS

For a positive weighted upper shift W, the Gram matrix (W-zI)* (W-zI)+eta I is tridiagonal with diagonal u,u+w_1^2,... and conjugate off-diagonal entries whose product is |z|^2 w_j^2. This yields exactly the recurrence (6), with u=|z|^2+eta. The determinant therefore depends on z only through rho=|z|^2.

The bridge lemma is valid for a general 2-by-2 matrix P over a commutative ring. With v=P v_0 and w=P f, one has R=v f^T+a w g^T and S=v f^T+b w g^T. Expanding the commutator gives the displayed expression. In f^T(RS-SR)v the two terms are the same product of commuting scalars, with opposite signs. Cayley-Hamilton expresses every nonnegative power of R as a scalar linear combination of R and I, giving the lemma for every n, without division or invertibility assumptions.

With P=K(1)^(m-1)K(t^2), the literal words produce f^T R^(m-1) S v and f^T S R^(m-1) v. The lemma equates their determinant polynomials for each fixed complex z. Equality of characteristic polynomials of the Hermitian positive semidefinite Gram matrices gives equality of all singular values, including multiplicities and zeros. This proves the required universal complex-shift condition; numerical sampling is not being used to establish it.

### 3. Numerator and nonzero denominator: PASS

The prefix-height formulas (11) follow directly from the motif and bridge increments. Telescoping products give (12). At vertices jD=jk+j, for 1<=j<=m, the X-height is 2; the row at vertex 0 consequently has m entries equal to t^2. The spectral norm dominates that row's Euclidean norm, proving ||p_m(X)|| >= t^2 sqrt(m). The Y-height difference from vertex 0 to N-1 is 2, so its highest-degree entry is t^2 and p_m(Y) is nonzero.

### 4. Uniform bound on each Y residue block: PASS

Residue classes modulo D=m+2 have size m or m+1. Every forward pair in a class is joined by one polynomial monomial. The exceptional height-0 vertices qk (q<m) have distinct residues -q, and the exceptional height-2 vertices mk+s (1<=s<=m) have distinct residues s-m. Thus each class contains at most one occurrence of either exceptional height.

Deleting the zero first column and zero last row preserves the operator norm. The resulting matrix is entrywise nonnegative and dominated by the outer product of vectors with entries t^(-a_i) and t^(a_(j+1)). Applying absolute values to an arbitrary complex input and then Cauchy-Schwarz justifies the spectral-norm bound; entrywise comparison is used only in this justified nonnegative setting. The exceptional-height counts give squared vector norms at most 1+(L-2)/t^2 and t^4+(L-2)t^2. Their product is (t^2+L-2)^2, giving ||p_m(Y)|| <= t^2+m-1 for all m,t in the stated domains.

### 5. Divergence and padding: PASS

Taking t=m gives the lower bound sqrt(m)/(1+(m-1)/m^2) >= (4/5)sqrt(m), since 4(m-1)<=m^2. This produces finite rational witnesses with arbitrarily large ratios. In particular, given any proposed nonnegative universal constant C, choosing an integer m>(5C/4)^2 (and m>=2) violates it. A single ratio greater than 1 would not suffice, but this unbounded family does.

For fixed m, taking the supremum over finite t yields C_(m+1)^2 >= sqrt(m), without asserting that the supremum is attained. Padding both matrices by the same zero block preserves super-identical pseudospectra. Because p_m(0)=0, it also preserves the polynomial norms. Thus Corollary 3, C_N >= sqrt(floor(sqrt(N))-1) for every N>=9, and its liminf conclusion are correct. Exact constants and the optimal growth rate remain undetermined.

## Independently reproduced computations

The new checker completed successfully with Python 3.14.6 and NumPy 2.5.1. Its exact portion uses only standard-library rational arithmetic and sparse polynomial arithmetic:

- Generic symbolic bridge cancellation and the 2-by-2 Cayley-Hamilton identity.
- Literal word, height, numerator and block bounds for m=2,...,100, including 5,247 residue classes and rational t close to 1.
- 15 complete bivariate determinant identities in u and rho, for m=2,...,6 and t=3/2,2,3.
- 54 independently assembled dense Gram determinant comparisons with rational real shifts and eta, for m=2,3,4.
- A deliberately incorrect motif was rejected by the determinant comparison.
- 280 complete singular-value comparisons for complex shifts, m=2,...,8. Maximum absolute discrepancy divided by the larger of 1 and the largest singular values: 3.36e-15.
- 28 direct dense polynomial-pair checks, including comparison with residue entries and the analytic norm bounds.

Computed ratios for t=m include 1.712768086 at m=4 (N=25), 2.742624520 at m=9 (N=100), and 6.864139181 at m=49 (N=2500), matching the rounded values in the submitted log. The large examples use residue blocks. Floating-point checks do not prove exact equality or guarantee relative accuracy of tiny singular values. Universal validity rests on the analytic proof reviewed above.

Reproduce the exact checks from the submission directory:

```bash
python3 independent_check.py --pdf proof.pdf
```

Add `--numeric` if NumPy is installed. The retained JSON includes checker/PDF hashes and actual run times. It does not claim repository CI or regeneration of canonical documents.

## References and scope

The definition and the cited upper bound agree with Ransford and Walsh, [arXiv:2109.14472v2](https://arxiv.org/pdf/2109.14472v2), Theorem 1.3. That paper's Theorem 1.4 is about similarity-transform conditioning, not the polynomial norm ratio disproved here. The supplied lower bound is compatible with their upper bound. The historical citation to Fortier Bourque and Ransford was checked bibliographically and through the canonical entry and later paper; access to the complete 2009 paper did not succeed in this review. The new proof is self-contained and does not depend on an unexamined theorem from that paper.

Targeted title/topic searches did not locate another resolution, but this was not a comprehensive novelty or priority investigation.

## PDF and submission findings

All four pages were rendered and visually inspected. The equations, page numbers, references and proof endings are legible; no clipping, overlapping text or broken mathematical glyphs was found. The proof has no visible author byline or manuscript date, and its PDF Author metadata is empty. Add authorship and a date in the manuscript or accompanying submission record; an affiliation is useful when applicable. Reference [3] would benefit from a direct, preferably immutable, link to MF-24. No mathematical rewrite was found necessary.

The later folder supplies the original scripts, self-review, preparation helper and TeX source. The proof source compiled successfully twice with pdfLaTeX (TeX Live 2024), producing four pages with text extraction identical to the submitted PDF and no warnings or over/underfull boxes. The original PDF is retained byte-for-byte; differing TeX versions and metadata mean the new binary is not claimed byte-identical. The package's claim of no independent audit describes its earlier development stage; current submission notices should additionally identify this separate informal AI-agent audit. Original verification records are retained unchanged, even when accompanying README or helper documentation is updated.

The repository permits complete independently audited arguments, including disclosed AI audits, to support Solved status. This report is evidence a maintainer can evaluate under that rule. Submitting initially as Solution claimed while requesting review is a conservative editorial choice, not a claim that the argument is only partial. No Lean verified status is supported or requested.

## Supplied-code and preparation-workflow audit

The original exact suite passed all reported categories: 18 bivariate determinant identities, six direct Gram characteristic-polynomial identities with eta/z/zbar symbolic, six direct polynomial/block decompositions, the exact positive-LDL certificates at m=t=4 and 9, and both negative controls. The numerical suite passed 1,080 shifted SVD comparisons, 24 dense/block norm comparisons, 133 bound checks including t=1e200, and its negative control. The maximum scaled absolute SVD discrepancy on this machine was 1.088e-14. All seven printed norm ratios agree with the submitted rounded table.

The original helper failed against the real repository before changing files. Two relevant issues were identified: its metadata parser retained Markdown hard-break spaces after Partially resolved; and its stored target hash did not match the actual canonical text. The complete canonical target was independently compared with the manuscript and then pinned to the exact reviewed text, hash af562e8a75efeb755df32a4ad795193c7187790a83505eb9a574b531ace291d1. The protection remains an exact hash check; it was not disabled or made to accept arbitrary targets. The preserved target snapshot is included in the reviewed preparation package. A macOS temporary-path alias also caused one original fixture test to fail; normalizing the checkout path fixes that comparison. The reviewed helper and its new Markdown-space regression passed all 45 supplied/extended fixture tests.

In a separate actual-repository clone at the reviewed base, the corrected helper copied the intended payload, preserved the target and registry, regenerated the indexes and canonical documents, and passed ID validation plus 17 permanent-ID tests. The additional repository suites passed: three status/count tests, 16 formatting tests and 11 math-rendering tests. The original working repository remained clean. These are local runs against actual repository tools, not a hosted GitHub CI run.

Visual inspection of the initial canonical regeneration revealed an almost-empty extra page caused by MF-24's existing forced break before References. The final publication instructions include a targeted removal of that obsolete break; the source mathematics is unchanged.

The final reference payload and reviewed helper were applied in a second actual-repository clone. ID validation and 17 ID tests passed again, the final renderer passed all 11 math-rendering tests, and git diff --check passed. The two-page final canonical PDF was visually inspected on both pages; the almost-empty page is eliminated. No mathematical target or registry mapping changed.
