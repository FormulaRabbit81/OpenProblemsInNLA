---
title: "MI-04 — A universal block-norm characterization of essentially Hermitian matrices"
author: "Matthew J. Colbrook"
affiliation: "Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom"
date: "11 September 2026"
catalog-status: "Lean verified"
formalization-author: "George Stepaniants"
formalization-affiliation: "Department of Computing and Mathematical Sciences, California Institute of Technology"
document-kind: "Resolution"
proof-source: "../../references/colbrook-matrix-2026-09-11/original-proofs/MI-04.tex"
preamble-source: "../../references/colbrook-matrix-2026-09-11/original-preamble.tex"
bibliography-source: "../../references/colbrook-matrix-2026-09-11/references.bib"
review-source: "../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-04-review.md"
---

# MI-04: affirmative result

**Author:** Matthew J. Colbrook.  
**Affiliation:** Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom.  
**Date:** 11 September 2026. **Catalog status:** Lean verified.

The universal positive-block operator-norm property holds exactly when the off-diagonal block is essentially Hermitian. The proof applies in every finite dimension without invertibility or distinct-singular-value assumptions.

This covers the exact universal target recorded in the original problem statement.

## Complete proof and independent verification

The complete authored proof is in [solution.pdf](solution.pdf) and its [standalone LaTeX source](solution.tex), **Theorem 1.1 and its proof**. This Markdown page is a submission note; the complete mathematical argument is the attached TeX/PDF. The [original proof](../../references/colbrook-matrix-2026-09-11/original-proofs/MI-04.tex) is embedded unchanged in the exported TeX.

A separate Codex agent returned [PASS](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-04-review.md) after checking the complete original argument against the exact catalog target. The full original SHA-256 after UTF-8 decoding and CRLF-to-LF normalization, without trimming, is `8363d460f59fba544577ba6453e44cec51f9b546a01875515361df352321fb7c`. The original draft was AI-assisted. Independent agent verification is not external human peer review or formal proof certification, and the review does not certify novelty or first-discovery priority.

The affiliation was verified from the [official Cambridge homepage](https://www.damtp.cam.ac.uk/user/mjc249/home.html). See the [submission record](../../references/colbrook-matrix-2026-09-11/README.md) for archived inputs, exact diagnostics, review scope and reproduction commands.
## Lean formalization - 16 September 2026

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, supplied the AI-assisted Lean formalization and verification submission. Matthew J. Colbrook retains authorship of the mathematical proof above.

The [immutable Lean proof](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/63340ef17139606dce03c4d9000288129b773157/matrix-inequalities-and-norms/MI-04/lean/Solution.lean) proves the full original necessity implication, with all positive complex dimensions and singular or repeated-value cases. Its 21 independently specified exports include `NLA.MI04.universal_positive_block_essentially_hermitian`. The stronger four-way equivalence in the mathematical manuscript is not an additional formal claim.

The coordinator's [source-bound audit](lean/verification/linux-2026-09-16/ROOT-AUDIT.json) accepted [canonical run 35150473054](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35150473054) at `63340ef17139606dce03c4d9000288129b773157`, covering all 233 inputs, 21 exports, default-kernel replay, Comparator and required controls. The independent [nonauthor runtime review](lean/reviews/canonical-runtime/REVIEW.md) also passed. The full original necessity implication is **Lean verified**; later publication-commit and upstream checks remain separate. The [verification note](lean/VERIFICATION-NOTE.md) distinguishes this formalization from the earlier informal agent review and gives the exact scope. No new mathematical priority or human endorsement is asserted.
