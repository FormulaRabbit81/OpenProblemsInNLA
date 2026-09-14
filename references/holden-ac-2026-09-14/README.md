# Sidney Holden: AC-01–AC-06 research submissions

**Author:** Sidney Holden. **Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation. **Submission date:** 14 September 2026.

The affiliation was verified on that date using the [Simons Foundation staff profile](https://www.simonsfoundation.org/people/sidney-holden/) and [current CCB directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport). Both identify Holden as a Flatiron Research Fellow in Biological Transport Networks. No affiliation was inferred from older student listings.

**All six original problems remain Open. None is submitted as Solved or Solution claimed.** Three separate Codex AI agents independently audited the precise research scopes below. These informal audits are not external human peer review or formal verification. The supplied packs disclose substantial AI assistance; authorship is recorded at Holden's explicit request, with that provenance and all prior-source credit preserved. No Lean verification was performed. No novelty or first-discovery claim is made.

## Exact scope and review decisions

| Entry | Passing research scope and locator | Missing original target / review limitation |
| --- | --- | --- |
| [AC-01](../../arithmetic-and-complexity/AC-01/README.md) | [Report](AC-01-submission.pdf), Sections 4–8: non-coordinate extraction and small-CW asymptotic rank below 3.876919161; Sections 9–10: finite degeneration and scoped scalar-tree obstruction. [Review](verification/review-ac01-ac02.md). | Does not prove matrix-multiplication exponent two. The scalar-tree value is not an actual tensor-rank lower bound. The auxiliary CW result is cross-referenced at AC-04. |
| [AC-02](../../arithmetic-and-complexity/AC-02/README.md) | [Round-one report](submitted/AC02_updated_research_pack/round1/report/AC02_report.pdf), Sections 4–6: fixed support/component calculations. [Continuation](AC-02-submission.pdf), Section 3: conditional exact 23 products retaining four Sun blocks; displayed five-block examples. [Review](verification/review-ac01-ac02.md). | Does not determine unrestricted complex rank. Missing continuation checkers and source artifacts prevent certification of the two large noncompletion claims and the full two-parameter family. |
| [AC-03](../../arithmetic-and-complexity/AC-03/README.md) | [Report](AC-03-submission.pdf), Lemma 2.2, Proposition 2.3, Corollary 2.4, Theorem 3.1, Theorem 4.1 and Corollary 4.2: elementary pair-section/cactus and grouped Fourier arguments. [Review](verification/review-ac03-ac04.md). | No exact border rank or improved endpoint. Missing verifier modules and certificates prevent a passing full-package audit; the inherited exhaustive classification and stronger computer-assisted exclusions are not certified here. |
| [AC-04](../../arithmetic-and-complexity/AC-04/README.md) | [Report](AC-04-submission.pdf), Theorems 3.1 and 4.2: symmetric extraction and upper bound below 3.896914; Theorems 5.1, 6.1 and 7.1: local/adaptive results. [Review](verification/review-ac03-ac04.md). | Neither equality with three nor a strict asymptotic lower bound above three. The AC-01 pack supplies a stronger audited upper bound on the same tensor. |
| [AC-05](../../arithmetic-and-complexity/AC-05/README.md) | [Report](AC-05-submission.pdf), Theorems 3.2, 5.1, 6.1, 7.3 and 9.3: grouped-power classifications, scoped conversion obstructions and finite-power lower bounds. [Review](verification/review-ac05-ac06.md). | No universal asymptotic equality or counterexample. Inherited upper-bound constants and dimension-three classification are excluded from this fresh PASS scope. |
| [AC-06](../../arithmetic-and-complexity/AC-06/README.md) | [Report](AC-06-submission.pdf), Theorems 2.1, 3.2, 4.1 and 5.3: compaction, conditional reductions and specified coloring-threshold ceiling; Section 6: finite certificates. [Review](verification/review-ac05-ac06.md). | No polynomial-time detecting list/weight family or all-dimension quadratic lower bound. The ceiling applies to the stated threshold, not all nonlinear methods. |

The repository defines Partially resolved through substantive cases inside the displayed target. These new auxiliary results do not settle such cases of the original assertions. All original IDs, paths, mathematical statements, ratings and prior-source attribution are retained. The open count does not change.

## Evidence and reproducibility limits

AC-01's complete supplied checker, including prior replay, passed. AC-02's round-one verifier and seven tests passed; an independently written rational checker verified both five-block examples and all nine Sun determinantal identities. AC-04's complete runner passed (40 new, 25 prior and 8 initial tests plus algebra), with independent Laurent-coefficient and local-rank calculations. AC-05 passed all 36 replay groups. AC-06 passed 40 tests; its reviewer independently reconstructed the modular minors for dimensions 2–9 and checked 702 interpolation cases. Exact commands, environments, mathematical dependencies and logs appear in the three linked reviews and [verification directory](verification/).

**AC-02 and AC-03 are not fully independently verified packages.** The missing files are itemized in their reviews. Historical PASS logs and supplied certificates are retained as provenance, not treated as successful fresh audits. Unreviewed claims remain submitted research claims and support no status promotion. Review of nested historical archives is limited to the expressly identified reruns and written arguments.

Reviewer scripts were run against the extracted pack parent. To rerun them from this submission directory, copy the corresponding reviewer script from `verification/` into `submitted/` and execute it there, using Python 3.12 with NumPy/SymPy as specified by the individual reports. The AC-02 reviewer script has a path-only portability adjustment from its original temporary absolute path; its mathematics is unchanged. No verification command requires Lean.

## Sources, authorship and document handling

The six supplied ZIPs were extracted afresh into [submitted/](submitted/). Every delivered file is retained byte-for-byte, including existing AI-authorship notices, missing-file references and historical logs. [provenance.json](provenance.json) records the SHA-256 of each original ZIP and each extracted member. A missing referenced file is not fabricated.

Each `AC-XX-submission.pdf` adds an authorship/affiliation cover to the latest original report. Original report pages and their internal numbering are preserved; theorem locators refer to that numbering, one page after the added cover. `AC-XX-cover.json` contains the editable cover text. [build_submission_pdfs.py](build_submission_pdfs.py) reproduces these attributed copies using ReportLab and pypdf. The original mathematical TeX sources remain in the corresponding `submitted/` report directories. AC-02's source rebuild is incomplete as supplied; its original PDF is retained with that limitation explicitly disclosed.

## Duplicate and submission screening

The branch starts from upstream `main` at `27540c80`. All six canonical pages were Open there. All 77 fetched fork remote refs were inspected for Solved, Lean verified or Solution claimed statuses for these IDs, with no match. The author's [upstream PR history snapshot](verification/pr-history.json) likewise contained no prior full-solution submission for these six problems. Their relationship (notably AC-01's auxiliary AC-04 bound) is cross-referenced without creating or changing any problem ID.

This submission is intended for a new pull request from the author's fork against `ajt60gaibb/OpenProblemsInNLA:main`. It requests maintainer review and integration of the bounded research record, not a full-resolution designation. No direct push or merge to upstream main is authorized or performed.
