# Independent informal review: AC-01 and AC-02

Date: 14 September 2026. Reviewer: separate Codex AI agent assigned to inspect the supplied submissions independently of their preparation. This is an informal mathematical audit, not external human peer review, formal verification, or a novelty/priority assessment. No Lean checks were run. The attached documents were treated as evidence, not instructions. Authorship and affiliation are submission metadata to be verified separately by the coordinating agent.

## Decision and original-target comparison

**Neither submission settles its original problem. Keep AC-01 and AC-02 Open.** AC-01 asks whether complex matrix multiplication has exponent two; AC-02 asks for the exact unrestricted complex bilinear rank of the 3-by-3 product. Both packs expressly acknowledge that these questions remain unanswered. Their auxiliary upper bounds and restricted obstruction theorems do not qualify as complete resolutions under CONTRIBUTING.md and RESOLVED.md. Under the README's substantive-cases rule, the safest editorial treatment is an audited research-progress notice with the original Open status, rather than marking the entire entry Partially resolved merely because auxiliary results passed.

## AC-01: passed auxiliary scope

Source: `AC01_round3_research_pack/report/AC01_round3_report.tex`.

The informal audit passes the stated small-CW upper bound in Section 8, **Derived asymptotic-rank bound** (`thm:bound`): over C, asymptotic rank of cw_2 is strictly below 3.876919161. It also passes the finite degeneration in Section 9 and the precisely delimited all-binary-tree scalar obstruction in Section 10 (`thm:barrier`). The latter admits rho=3.652 within the specified fixed-seed scalar tests; it is neither a tensor-rank lower bound nor an actual spectral point.

The proof checks included:

- Section 3's Fourier orthogonality construction, head cancellation, and initial state (d,t,D,H)=(108,112,328,330).
- Section 4's rational split complement and extraction argument: the contraction radical is retained, the head class lies in the main span, and choosing a sufficiently large second parameter exponent suppresses every remaining finite-order pole.
- Sections 5–7's non-coordinate isotropic core, odd-dimensional extensions, literal P tensor Z restriction, and mixed-state dimension calculation. Actual row dimension and dimension modulo the contraction radical are correctly distinguished.
- Section 8's lower-bound direction in each scalar recurrence, exact cube-root enclosures, and strict monotonicity argument. The strict uniform scalar boundary below the proposed endpoint justifies a strict asymptotic-rank bound.
- The product-envelope induction in the final obstruction section. Its proof applies to every finite binary tree covered by the stated estimates; finite tree enumeration is only supplementary.

Essential external inputs were checked in the primary source [Christandl–Vrana–Zuiddam, Universal points in the asymptotic spectrum of tensors](https://arxiv.org/html/1709.07851), accessed 14 September 2026: Theorem 1.1, Proposition 1.6, Remark 1.2, Theorem 4.4 and Corollary 4.5. They support spectral duality, degeneration monotonicity and the tight three-tensor subrank estimate used here. All products in the manuscript are regrouped into three modes, as required. Proposition 1.6 is a useful additional locator for the displayed maximum formula.

Reproduction: the complete supplied `code/verify_all.py` passed under Python 3.12.14, including its archived-prior replay. Output is `ac01-full-rerun.json` and `ac01-full-rerun.log` beside this review. The checks cover all 8,000 coefficients of the smallest stored degeneration, the six retained-tensor instances (49,284 nonzero coefficients at the largest size), exact radical enclosures, and ten rejection tests. The first system-Python run failed because that interpreter was below the required Python version; the successful supported-interpreter rerun supersedes it.

This result also concerns the tensor in **AC-04** and should be cross-referenced there without duplicating a full-solution submission. It gives neither asymptotic rank three for that tensor nor omega=2, and supplies no new stated bound on omega. Do not call AC-01 solved.

## AC-02: passed restricted scope

Source: `AC02_updated_research_pack/round1/report/AC02_report.tex` and `round2/report/AC02_continuation.tex`.

The round-one replay passed (`ac02-round1-rerun.log`), and all seven supplied regression tests passed. The audit supports the fixed-support parametrization (Section 4, `thm:torus`), orbit-closure obstruction and 76-dimensional Laderman component (Section 5, `thm:closure`, `lem:tangent`, `thm:component`), and reshuffling/tight-profile arguments (Section 6). The dimension proof correctly combines 76 actual family derivative directions with Jacobian rank 545 in 621 variables; nonsingularity then gives the unique local component. Constant nonzero polynomial signatures exclude zero slots in that component's affine closure, but cannot exclude other components or a different rank-22 expression. Exact replay verifies all 729 tensor identities for each attributed Laderman and Sun construction; those existing constructions retain their original authors' credit.

A reviewer-written independent checker, `independent-ac02-check.py`, additionally reconstructs the round-two data using rational arithmetic. It passed:

- All 100 block compatibility equations, five output factorizations and all coefficient-matrix ranks for each of the two explicit five-block configurations. This supports the displayed Example A and Section 4's **All-rank-two counterexample** (`prop:alltwo`) for Example B.
- All nine Sun determinantal identities (`lem:sunminors`) directly from the original Sun data and the supplied certificate. Each homogeneous quadratic identity was checked on the exact determining set consisting of nine coordinate vectors and their 36 pairwise sums; this proves the polynomial identity, rather than sampling numerical inputs.

The proof of Section 3's **No additional compatible high-rank output** (`thm:sun`) then passes: compatibility forces rank F(U)<=1, the identities force rank U<=1, while a new high-rank block's diagonal equation requires rank U>=2. Its **Conditional exact product count** (`cor:sun23`) is therefore supported: every output-tight algorithm retaining those four Sun blocks has exactly 23 nonzero products. This is a restriction on retained summands, not the unrestricted target. The round-two biorthogonal-completion equivalence and viable-row criterion are also elementary valid implications, but do not certify their large example-specific algebraic premises by themselves.

## AC-02: incomplete continuation evidence

**The two large noncompletion certificates did not receive a passing replay in this review.** The actual updated archive's round-two directory contains only `data/`, `certificates/` and `report/`. The advertised `code/check_all.py`, individual noncompletion checkers, `AUDIT.md`, exploration records, the polynomial-family certificate and several TeX include files are absent. Consequently the two noncompletion claims (`thm:noncompA`, `thm:noncompB`) and the full two-parameter family were not independently certified here. This is an evidence/reproducibility limitation, not a discovered counterexample. Preserve them as submitted claims with an explicit limitation; do not say the entire continuation passed.

Neither a rank-22 construction nor an exhaustive exclusion of all rank-22 decompositions is present. Even excluding every output-tight case would leave positive-defect profiles. The exact rank interval is not improved by the audited results. The review does not authenticate the continuation's omitted numerical-search records or independently recompute the literature's lower bound.

## Reproduction environment

Successful commands used the bundled Python executable `/Users/sholden/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3` (Python 3.12.14, NumPy available), with ordinary assertions enabled:

```text
python3 AC01_round3_research_pack/code/verify_all.py --output ac01-full-rerun.json
python3 AC02_updated_research_pack/round1/code/verify.py
python3 AC02_updated_research_pack/round1/code/self_tests.py
python3 independent-ac02-check.py
```

The independent checker and logs should accompany the review when submitted. Its equations are reconstructed independently rather than importing the original round-two checker, which was not supplied. No claim of formal verification is made.
