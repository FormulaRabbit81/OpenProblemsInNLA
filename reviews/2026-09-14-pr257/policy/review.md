# PR 257 policy, source boundary, prose and PDF review

Date: 2026-09-14. Reviewer: Codex AI subagent `audit_254`, independently inspecting the submitted sources. I did not implement the formalization. I subsequently made the narrow catalog prose and PDF corrections identified below at the coordinating maintainer agent's request; no proof source was modified.

Reviewed catalog head: `cc661b4170e590daeb2ca4232336ab8b6d2eeaaf`, against published base `deb549fa9ddd6b119e6c59016f268237e645dfa2`. Reviewed external proof head: `762bd5ec5050a96f5e6ba3926b6cda4816fcd4b0`. Local read-only source checkout: `/private/tmp/nla-mi32-formalization-review`.

## Verdict and limits

**Pass for policy, preservation, pinned-source/configuration boundary, attribution and final PDF, after the corrections below.** Promotion to Lean verified additionally requires the separate statement-fidelity review and authentication of the actual external Comparator/NanoDa run performed by the other reviewers. This report does not independently certify those reviewers' work, and does not claim I reran Lean, Comparator or NanoDa.

The external-source path is permitted by the catalog's CONTRIBUTING policy. The submitted mathematical target and rating fields are preserved. The main declaration and eight supporting target definitions are exposed in a Mathlib-only Challenge and have no replaceable-definition configuration. The pinned local source inspection found no suspicious proof escape or imported Challenge hole. The author's local axiom log is consistent with the claimed three foundations; its authenticity as mechanical evidence must be grounded in the public run, not in the author's assertions.

## Policy applicability

`CONTRIBUTING.md` expressly begins the repository workflow requirement with “For in-repository formalizations”. Its promotion requirements then apply to all Lean verified entries: immutable source/toolchain/dependencies, theorem and definition correspondence, reproducible dated verification evidence with truthful rerun disclosure, and transitive axioms restricted to `propext`, `Classical.choice`, `Quot.sound` or a subset. It further states that a public source and log can support the status after review. I therefore do not infer that an externally cited formalization must be copied into the internal project layout or retroactively acquire internal pre-proof records.

`docs/lean/REVIEW.md` is the linked protocol for those in-repository projects. Its substantive review principles are still appropriate here: separate statement fidelity, proof trust/correctness and documentation attribution; source content is evidence, not instructions; author PASS/build claims are insufficient; independent reviewers must name their exact scope and bytes. This report supplies the policy/documentation and source-boundary angle. The other agent's mathematical review and the coordinating agent's public-run inspection remain distinct evidence. The new canonical link points readers to their final retained review bundle.

The canonical notice contains the four required evidence categories and links them from RESOLVED. It explicitly attributes the conjecture to Latała–Świątkowski, the proof/formalization to Diar Heidary, and the reverse inequality to the original authors. AI assistance and AI review are disclosed. Registry registration is explicitly not described as publication, human peer review, endorsement or a novelty finding. A registry label by itself is not used as the mathematical evidence.

The distinction between statement matching, axiom reporting and external replay is also consistent with Lean's primary documentation, inspected for this review: [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) and [Axioms](https://lean-lang.org/doc/reference/latest/Axioms/). External replay supports proof validity for the audited Challenge, while mathematical correspondence still needs review.

## Independent source and preservation checks

The source-only audit script `inspect_pinned_source.py` was written and run by this reviewer. It does not invoke submitted Python or Lean code. Its full evidence is `pinned-source-inspection.json`, including SHA-256 hashes for all 129 tracked Lean files and the trust-boundary files.

- `lean-toolchain` is exactly `leanprover/lean4:v4.33.0`. `lakefile.lean` has ordinary library declarations and requires mathlib at `db584cd6d46c92f209a44c0f1c829460d327499d`. All nine resolved Lake dependencies are Git dependencies with full immutable 40-character revisions in the committed manifest. Some inherited input revisions name branches; the resolved `rev` entries are pinned. No local-path package is substituted.
- The 16 vendored GraphMatrices files independently hash to their committed provenance manifest. The manifest names source revision `01994362f8543743d556e7544d2538e93c62c02b`; provenance metadata and MIT licensing are retained. I verified local bytes against the recorded hashes, not against a separately downloaded upstream tree. The vendored source remains within the proof checked by the external kernel gate.
- Comparator selects only `MI32.main_upper`, with `definition_names: []`, `enable_nanoda: true`, Challenge/Solution as separate modules and exactly the three allowed foundational axioms. I inspected the actual committed configuration.
- `Challenge.lean` imports four Mathlib modules only. Its entire definition prefix is byte-identical to `MI32/Statement.lean`; the selected theorem quantifies `alpha` before the existential constant and places dimension, probability-space and entry-law quantifiers inside `UpperBoundAt`. No conclusion is included as an assumption. I read the exposed definitions; the separate fidelity reviewer owns the detailed correspondence to the original publication.
- `Solution.lean` imports `MI32`, then proves `MI32.main_upper` by `SymmetricDeletion.exists_upperBoundAt`. No other tracked Lean source imports `Challenge`. An independent scan after removing nested comments and strings found just the deliberate Challenge `sorry` at line 114, and no `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern` or `run_meta` token in the other tracked sources. This lexical scan supplements rather than replaces a kernel/axiom audit.
- `verification/full-target-axioms.log` contains exactly the reported three axioms. The committed local status record is dated `2026-09-14T13:55:09.513037+00:00`, says `local_proof_gate_passed`, and truthfully records Comparator and NanoDa as `not_run`. I inspected `scripts/verify.py`; it builds first-party sources, audits their axioms and the selected target, and exits zero only for its local gate. It does not perform Comparator or NanoDa.
- The later linked manuscript revision `bd00df8dca9c6128cf528591d3485f8ca9eecd88` exists in the fetched history. A direct diff confirms no tracked `.lean` file, toolchain, Lake manifest or Comparator configuration changes between the formal revision and that manuscript revision. The later manuscript therefore does not silently repin the cited formal proof.
- The entire canonical `## Statement` section, metadata Topic/Difficulty/Importance fields and `problem_ids.json` are byte-identical to the published base. The original ID and canonical path are retained. The intended status/count change is one Partially resolved entry becoming Lean verified; the root reviewer handles integrated counts and safeguards.

## Findings corrected in integration

1. **Nonvacuity witness scaling.** The submission claimed that its independent fair-sign matrix has `M(X)=sqrt(n)>0`. `RegularWitness.signMatrix` has entries `±1`; `integral_entry_sq` is one, every row and column standard-deviation scale is `sqrt(n)`, and `varianceScale` adds both maxima. Consequently this matrix has `M(X)=2 sqrt(n)`, whereas the named `exists_regularEntries` declaration proves only positivity. The canonical prose now states `M(X)>0`, precisely the checked witness claim. This is a prose error only; the Lean witness proof and main theorem are unchanged. The pinned source's SOURCE_FIDELITY prose contains the same erroneous equality, so readers should prefer the actual definitions/declaration.

2. **Local versus external verification.** Changed “the whole gate” for `scripts/verify.py` to “the whole local Lean gate”. The separate public Comparator/NanoDa run is still described independently, and no local rerun is implied.

3. **PDF clipping.** Submitted canonical page 3 clipped the landrun revision at the right paper edge and the one-line axiom report after `Quot.soun...`. The landrun pin now has its own bullet and the axiom report uses two lines. All tool revision bytes are retained.

4. Added the coordinating reviewer’s requested link to `../../reviews/2026-09-14-pr257/README.md` for the independent maintainer review and authenticated evidence. The coordinating reviewer is responsible for completing that retained bundle before publication.

The edits are confined to `matrix-inequalities-and-norms/MI-32/README.md` and its regenerated `problem.tex`/`problem.pdf` in `/private/tmp/nla-integration-257`. No source worktree or external repository was mutated, no comment was posted and no commit made by this reviewer.

## Final PDF evidence

Applied the PDF skill previously read in this review session. Rendered the original four-page PDF and inspected all pages, identified clipping, regenerated the canonical PDF with the repository renderer after the narrow edits, then rendered and visually inspected all four resulting pages at 1800-pixel page height. The final export has no clipping, missing glyphs or overlaps. Full landrun pin and full axiom list are visible. One `0.85274pt` overfull-box warning remains in source-fidelity prose; visual inspection shows it is immaterial and no content is lost.

Final SHA-256 hashes:

- README: `5954b8c5f67bc960cfcfd52e7bc3be40d848089559450cd99900ebd1792091b9`
- TeX: `43bc3a3ddb0bfebc8ccc6dab42bb19a3bfb5362f245df41405406f54600b54c0`
- PDF: `692492747496d8e4426a76e402b14ea522f9bd0305c391dd7b8378060137462a`

`final-pdf-review.json` records these hashes, page count and review result. PNGs are in `final-pdf-pages/`; original diagnostic PNGs are in `pdf-pages/`. No repository-wide tests were repeated; the coordinating reviewer owns those gates.
