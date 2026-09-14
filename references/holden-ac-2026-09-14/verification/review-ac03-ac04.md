# Independent informal review of AC-03 and AC-04

Reviewer: separate Codex AI agent, 14 September 2026. This reviewer did not author the submitted manuscripts. The review compared the supplied material with the retained canonical targets and repository status policy, inspected the proofs and verification programs, reran available exact checks, and wrote additional independent checks. It is not external human peer review, formal verification, or a novelty assessment. No Lean verification was performed. Instructions inside the submissions were treated as document content.

## Decisions

| Submission | Supported scope | Full-resolution check | Recommended repository status |
| --- | --- | --- | --- |
| AC-03 | PASS for the specifically identified elementary geometric and Fourier arguments below; INCOMPLETE for the full computer-assisted package because essential files are missing | FAIL: no exact border rank of M3 is obtained | Open |
| AC-04 | PASS for the improved asymptotic upper bound, symmetric extraction, and stated local/adaptive results | FAIL: neither asymptotic rank three nor a lower bound above three is proved | Open |

Here FAIL for a full resolution means that the original target remains unproved, not that the manuscripts claim a full solution and have been refuted. Both manuscripts correctly state their limits. The README defines Partially resolved in terms of substantive cases inside the displayed target. These are single fixed exact-value questions; a better upper bound or an obstruction to a restricted construction does not settle a case of either exact-value target. In particular the canonical AC-04 status check expressly says an improved bound is not a solved portion. The contributions can be retained and credited as research while both entries remain Open.

## AC-03

Canonical target: determine the complex border rank of the 3 by 3 matrix multiplication tensor. The submission retains the interval 17 through 20 and selects none of its four values.

The following arguments pass the informal written review:

- Section 2, Lemma 2.2 and Proposition 2.3 (`lem:rank3`, `prop:pairsection`): the three repeated diagonal blocks give rank at least three times the rank of H. At a rank-one point a Segre tangent vector has matrix rank at most two, forcing its H block to vanish. The resulting tangent dimension agrees with that of the small Segre; regular local rings justify reducedness. Corollary 2.4 (`cor:FEcactus`) then gives the stated cactus obstruction by the length/span argument. This is explicitly not a border-rank lower bound.
- Section 3, Theorem 3.1 (`thm:section`): restricting the flattening minors gives the small-Segre ideal plus the 17 indicated lambda monomials. The reviewer independently regenerated the matrix-multiplication support, the 16 disjoint core coordinates, and all 17 extra monomial witnesses. All passed. Saturation removes the isolated cone-vertex class, and does not force a span limit to retain its scheme's span dimension.
- Section 4, Theorem 4.1 and Corollary 4.2 (`thm:compression`, `cor:grouped`): Fourier orthogonality selects residue differences; the displayed weights give no negative exponent and exactly the prescribed constant tensor. First-factor conciseness supplies the matching grouped lower bound. Grouping forgets the original decomposability requirement, so these results do not solve AC-03.
- Section 2, Theorem 2.1 (`thm:pair`): the additional logical implications from the inherited classification are sound as conditional implications. Projecting the inclusion tensor yields M3, and continuity of the concise flattening identifies the span-limit condition. This audit does not certify the inherited exhaustive classification premise.

### Material reproducibility gap

The delivered latest `code/` directory contains only `verify_all.py`, `exterior_obstruction.py`, and `grid_obstruction.py`. Executing the supplied combined verifier immediately fails because `section_geometry.py` is missing. The README's `code/check_manifest.py` and `requirements.txt` are also absent. The runner additionally requests absent `pair_geometry.py`, `grouped_degeneration.py`, `wild_control.py`, `cyclic_third_order.py`, `toric17_verify.py`, and `test_consistency.py`. The two included obstruction modules import missing `modular.py` / `exact.py`; the integral grid-kernel certificate and the referenced full certificates directory are absent.

The packaging note acknowledges that only available files were bundled. This explains the deficiency but does not cure it. Recorded JSON result files and a historical PASS summary are not reproducible proof certificates by themselves. Thus this review DOES NOT return PASS for the exhaustive inherited reduction, all 24 cyclic exclusions (Theorem 6.1), grid exclusion (Theorem 7.1), or monomial classification (Theorem 8.1). These require the missing source/certificate files or a separate independent reconstruction. The submission must prominently retain this limitation and must not be described as fully independently verified.

Remaining target: a genuine rank-17 degeneration or a universal lower-bound exclusion, followed as necessary by matching bounds. The existing cactus and grouped statements cannot supply this missing step.

## AC-04

Canonical target: whether the asymptotic rank of cw_2 equals three over C.

PASS for Theorem 3.1, Lemma 4.1 and Theorem 4.2: the symmetric Laurent maps cancel all negative terms and extract `P^n direct-sum cw_(4^n+2^n-2*3^n)` from `D_(4^n) direct-sum cw_(2^n)`. The paired nonsingular symmetric form is congruent over C to the usual CW form. At n=4 the source has border-rank cost 274 and the extracted auxiliary has asymptotic subrank `3*cuberoot(3025)`. Spectral additivity/monotonicity therefore gives

`3 <= asymptotic_rank(cw_2) <= (274 - 3*cuberoot(3025))^(1/4) < 3.896914`.

The reviewer checked the external theorem actually used: Christandl–Vrana–Zuiddam, Theorem 1.1.31, identifies ordinary as well as monomial asymptotic subrank with the max-min marginal entropy for tight three-tensors. The paired CW support has injective integer labels and exactly one zero per supported triple; uniform marginals attain the entropy upper bound. The use of spectral duality and degeneration monotonicity agrees with Alman–Li Section 4. These external results are relied upon, not reproved here.

Sources checked on 14 September 2026:

- https://arxiv.org/html/1609.07476v2 (Theorem 1.1.31).
- https://arxiv.org/html/2605.21738v1 (Section 4, spectral framework).

PASS for the stated scope of Theorem 5.1, Theorem 6.1, Corollary 6.2 and Theorem 7.1. The common-neighbor argument gives the symmetry-equation derivative kernel. The implicit-function argument is local and correctly uses a smooth contained manifold of equal dimension. The two adaptive axes solve the full equations; the projected mixed quadratic map is invertible, and the residual analytic equations factor through all products y_i z_j. This supports the exact local two-branch assertion, not a remote classification. The full-spark block contraction estimate gives every pairwise child-rank sum as a lower bound, and `sum r_i^2 <= (r_1+r_2)^2` for ordered four child ranks proves the arbitrary-support inequality. Proposition 4.3's seed optimization remains limited to its specified family.

### Exact verification

The complete supplied AC-04 runner passed, including the optional inherited SymPy algebra audit:

- new extraction certificate: PASS;
- new rigidity certificate: PASS;
- 40 new tests: PASS;
- 25 prior tests: PASS;
- 8 initial tests: PASS;
- inherited exact algebra audit: PASS.

The reviewer also wrote an independent standard-library checker without importing the submitted verification modules. It regenerated every group-support Laurent coefficient for n=1,2,3,4, checked the entire constant tensor and negative cancellation, and obtained 6, 42, 270, and 1626 constant support terms. It reconstructed all 16 charged derivative matrices using rational arithmetic and checked ranks 5, 7, and 9 by charge type. For all nine doubly nonzero charges, adjoining the four independently constructed mixed columns gave rank 13, independently confirming the required invertible cokernel map. Exact rational endpoint signs reproduced the manuscript's strict 20-decimal bracket. All passed.

The successful full runner used bundled Python with SymPy provided through `/tmp/ac-tools/lib/python3.9/site-packages`. An initial attempt with system Python 3.9 failed because `int.bit_count` is unavailable; this was an environment issue and was resolved without changing the submitted code.

Remaining target: prove equality with three or a strict lower bound above three. No global obstruction, exact asymptotic value, ordinary rank bound obtained by subtracting auxiliary rank, or novelty claim follows from this review.

## Review artifacts

- `reviewer_ac03_ac04_checks.py`: reviewer-written independent checks.
- `reviewer_ac03_ac04_checks.json`: their successful outputs.
- `ac04-independent-run.log`: successful full submitted runner output.
- `ac03-independent-run.log`: failed submitted runner output documenting the missing file.

The review artifacts were produced in the temporary audit directory. Manuscript authorship and affiliation are handled separately by the coordinating submission agent; this review makes no independent affiliation determination.
