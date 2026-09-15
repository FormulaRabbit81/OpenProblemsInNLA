# PR264 independent preservation, renderer, and PDF review

**PASS, including the final integration PDF.** The submitted source is `32b028cf16e210f8f628ab1cc7c8f5b389df0632`; its published base is `6d840cd6bdf811e166ba0a07501407fb121ff0ce`. This bounded review independently checks target preservation, presentation, source status arithmetic, and renderer scope. Mathematical proof and computational reproduction are covered by separate reviewers.

## Original target and status

MF-24's original Problem statement explicitly asks whether `sup_N C_N < infinity`. Its prior scope paragraph explicitly identifies the unknown absolute constant as the admission target. Sharp values and optimal growth of `C_N` are identified as a related quantitative question. A valid family with unbounded polynomial norm ratios therefore settles the registered target negatively. The remaining optimal-growth question does not require retaining a Partially resolved status for the original boundedness question. The final **Solved** designation is appropriate subject to the separate complete-proof audit.

All **217** registered IDs and canonical paths are unchanged. **216** canonical READMEs are byte-identical to the base. For MF-24, removing the resolution notice, restoring its status/check date, and undoing the explicit historical-section label recovers the entire original README exactly. Its Problem statement, definitions, quantifiers, ratings, rationale, prior citations and prior literature-search record remain intact. The standalone checker also compares all original canonical Markdown links with multiplicity.

No prior tracked file is deleted or changed in mode or type. All **4,326** prior files under `references/` retain identical Git objects. The source modifies exactly eight existing files: root README, CATALOG, RESOLVED, the category README, MF-24 README/TeX/PDF, and the renderer. Its fourteen additions are confined to `references/mf24-counterexample/`. RESOLVED retains its complete previous text around the new MF-24 entry.

The submitted **Solution claimed** status and indexes agree: **42 Open + 71 Partially resolved = 113 open targets**, with **104 other retained entries**. The source evidence counts stay at **72 Solved and 31 Lean verified**. The category count is **13 open targets and 12 retained entries**. A later upgrade to Solved keeps the 113 open-target count and changes the Solved evidence count to 73; final index regeneration and repository checks are handled by the integrating reviewer.

## Renderer and presentation

The source renderer edit removes only the string `MF-24` from the set that inserts a forced page break before References. Exact source comparison and an independent AST inspection show that no other registered ID changes membership or rendering behavior. With the longer resolution notice, the submitted PDF already continues its Problem statement on page two. Keeping the old forced break would start References on another page, so removing it is justified.

All **four pages** of the submitted proof PDF were rendered with Poppler and visually inspected alongside its TeX. Theorem 1 and equations (1)–(5), Lemma 2 and equations (6)–(10), the denominator argument and equations (11)–(14), and equation (15), Corollary 3, equation (16), and the bibliography correspond to the source. No clipping, overlap, missing glyphs, unresolved citations, or illegible mathematics was found.

Both pages of the submitted canonical PDF were inspected. The original question split across pages, leaving its displayed inequality on page one and its universal quantifiers on page two. This review requested adding MF-24 to the existing renderer rule that starts Context and notation on a fresh page.

The integrating reviewer made that change and supplied a fresh **two-page** PDF from `/private/tmp/nla-integration-264`. Both final pages have now been visually inspected. Page one clearly displays **Solved**, credits **Georg Maierhofer (University of Cambridge)**, and distinguishes the manuscript date **14 September 2026** from the fresh audit date **15 September 2026**. Page two keeps the complete original definitions, quantified Problem statement, prior references and historical literature record together. It is legible, with no clipping, overlap, or missing glyphs. The final README from Context and notation onward is byte-identical to the submitted source; the corresponding final TeX is identical after ignoring whitespace. The proof PDF remains byte-identical to the submission.

## Primary-source cross-check and limits

Freshly read [Ransford–Walsh, arXiv:2109.14472v2](https://arxiv.org/pdf/2109.14472v2), printed page 3, for the exact super-identical-pseudospectra definition and Theorem 1.3's strict `sqrt(N-2)` upper bound for `N >= 4` unless both polynomial matrices vanish. Printed page 11, Proposition 5.1 and its following argument, confirms `C_4 = sqrt(2)` as a supremum. Theorem 1.4 concerns condition numbers of similarity transforms, a different quantity. The [arXiv version record](https://arxiv.org/abs/2109.14472v2) still lists v2, 9 July 2022.

The [2009 publisher record](https://academic.oup.com/jlms/article-abstract/79/2/511/860814) confirms the paper and its SIP definition. Its full text was not accessible in this bounded fresh check, so the exact inherited page-513 question locator was not independently re-opened here. This limit does not affect the direct preservation comparison with the immutable original MF-24 target. No new novelty or exhaustive literature-search claim is made. Author affiliation verification is handled by the integrating reviewer; this review checks its final presentation.

No PDF was authored or edited by this reviewer. PDF/TeX matching was checked by reading all pages alongside the source, without recompiling the proof. This review neither duplicates nor substitutes for the independent proof and computational audits.

## Compact evidence

- `check_preservation.py`: standalone Python standard-library checker using read-only Git commands; no repository or submitted code is imported or executed.
- `preservation.json`: source/base object comparison, status counts, scope, and SHA-256 hashes of every changed or added source file plus the registry.
- `pdf-review.json`: page-by-page review scope and separate hashes for the final canonical README, TeX and PDF. The integration was not yet committed at visual review, so these content hashes identify the exact reviewed outputs.
- `SHA256SUMS`: hashes of the compact report and evidence files.

Offline reproduction of the source-preservation check:

```sh
python3 check_preservation.py --repo /path/to/OpenProblemsInNLA --output /tmp/pr264-preservation.json
```

The checkout must contain both exact commits. Scratch `qa/` images and extracted text are excluded from the compact publication bundle.
