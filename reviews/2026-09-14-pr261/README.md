# Maintainer audit of PR #261

**Decision: accept the bounded research record; AC-01–AC-06 remain Open.**
This fresh informal AI audit was performed on 14 September 2026. It is not
external human peer review, a novelty determination, or formal/Lean verification.

- Source: [PR #261](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/261),
  commit `9bf50028bc30e6cdf78e19089befcb9b9bd6c292`.
- Published base: `27540c8022a33fef171625b7e48a95e33562d535`.
- Source tree: `9c92a5fe8201ffa0026687606a402deb0e16c14a`.
- Source-preserving integration merge: `800372c3147300ae9906a11aab3d5f919a057a37`.

The source adds six research notices and their supplied reports. The integration
adds this review record and a link from the submission README. Original targets,
ratings, statuses, prior references and submitted mathematical files are retained.
The independent reviews below supersede neither the original manuscripts nor
their disclosed limitations; they record exactly what was checked afresh.

## Mathematical scope

| Problem | Accepted scope | Reason it remains Open |
| --- | --- | --- |
| AC-01 | Non-coordinate extraction and the auxiliary small-CW asymptotic-rank upper bound below 3.876919161; finite degeneration and a scalar-tree obstruction. | No proof that the matrix-multiplication exponent is two. The scalar-tree value is not a tensor-rank lower bound. |
| AC-02 | Round-one support/component arguments; the conditional four-block exact-23 result; the two displayed five-block examples. | Unrestricted complex rank is not determined. Missing continuation artifacts prevent certification of the large noncompletion claims and full two-parameter family. |
| AC-03 | The specified elementary pair-section/cactus, ideal/saturation and grouped Fourier arguments. | No improved border-rank endpoint. The combined verifier cannot run because modules and certificates are missing; exhaustive classification and stronger computer-assisted exclusions are not certified. |
| AC-04 | Symmetric extraction bound below 3.896914 and the specified local/adaptive statements. The stronger AC-01 bound is cross-referenced. | Neither asymptotic rank three nor a strict asymptotic lower bound above three is established. |
| AC-05 | Grouped-power classifications, restricted conversion/catalyst obstructions and finite-power lower bounds. | No universal minimal-asymptotic-rank theorem or counterexample; the finite lower bounds have growth base three. Inherited upper bounds and prior dimension-three classification are outside this fresh audit. |
| AC-06 | CRT/interpolation compaction, conditional reductions, the specified coloring-threshold ceiling and finite Koszul certificates. | No efficient detecting list or weight family, and no all-dimension quadratic lower bound. The ceiling restricts the stated threshold, not every nonlinear method. |

Three separately assigned mathematical reviewers read the current written
arguments, checked applicable primary-source hypotheses, inspected executable
code before running it in scratch copies, and made fresh independent checks:

- [AC-01 and AC-04](ac01-ac04/review.md).
- [AC-02 and AC-03](ac02-ac03/review.md).
- [AC-05 and AC-06](ac05-ac06/README.md).

These records distinguish direct proof review from finite computational evidence.
Historical PASS logs alone are not fresh verification. AC-02 and AC-03 are
accepted only with the explicit missing-artifact exclusions already present in
their canonical notices. The supplied AC-05/AC-06 review has a nonblocking
locator typo: AC-06's controlled-list corollary is **2.3**, not 2.2. The fresh
review uses the correct number; the historical document is preserved.

The existing extreme difficulty ratings remain appropriate. AC-01, AC-04,
AC-05 and AC-06 retain broadly interesting importance; AC-02 and AC-03 retain
interesting to the community. None of the accepted auxiliary results settles
a substantive case of its original target that would justify a status promotion.

## Identity, provenance and documents

[Preservation checks](root/preservation.json) retain all 25,761 base paths and
all 217 registered IDs. The source modifies only the six canonical
README/TeX/PDF triples and inserts a research section in `RESOLVED.md`; all
other prior files are unchanged. Removing each appended notice and restoring
the prior check date recovers its original canonical README exactly.
An [independent preservation cross-check](preservation-independent/README.md)
also checks the source changes and submission membership.

All **227** extracted submitted members were freshly hashed against
`provenance.json`, with exact inventory equality. The original top-level ZIPs
are not retained in the repository, so their recorded container hashes are
submission provenance, not independently authenticated by this audit.
Nested ZIP members are covered as retained byte sequences; this does not
certify every claim inside them.

All **105** original report pages retain the same PDF page content streams,
boxes, extracted text, and normalized resource graphs, including decoded
embedded font/image bytes, after the six attribution covers were added.
See [page preservation](root/preservation.json) and
[resource preservation](root/pdf-resource-preservation.json). The reviewers'
records document visual inspection of the canonical PDFs and attributed
reports. No PDF was edited during this maintainer audit.

The contributor's stated affiliation is supported by the current
[official staff profile](https://www.simonsfoundation.org/people/sidney-holden/).
The directory URL did not load in this audit; the profile supplied the fresh
check. Authorship remains contributor-asserted, and all supplied AI-assistance
disclosures and previous-source credit remain intact.

## Repository validation and reproduction

- [All 77 repository tests passed](root/full-tests.log) at the source tree.
- The required permanent-ID validator, catalog regeneration and
  [17 ID tests](root/id-tests.log) passed in the integration worktree.
- Regenerating indexes made no change: 217 retained problems, 114 open
  targets (42 Open and 72 Partially resolved), 72 Solved and 31 Lean verified.
- New notice/submission [local links resolve](root/new-link-check.json).
- [Lean selection is empty](root/lean-selection.json); no in-repository
  formalization or verification harness changed.
- The full source diff contains Markdown hard-break spaces and preserved raw
  submission whitespace. It is not represented as globally whitespace-clean.

Run the preservation scripts with Python and pypdf, against a checkout whose
Git history contains the recorded base and source commits:

```sh
python3 reviews/2026-09-14-pr261/root/preservation.py --repo . --out /tmp/pr261-preservation.json
python3 reviews/2026-09-14-pr261/root/pdf_resources.py --repo . --out /tmp/pr261-pdf-resources.json
```

Each mathematical review gives its reproduction commands and environment.
Root environment details are in [environment.json](root/environment.json).
`SHA256SUMS` binds all files in this audit directory except itself. Final
GitHub workflow and publication receipts are recorded on the integration PR
so they can bind its final commit without changing the tree after testing.
