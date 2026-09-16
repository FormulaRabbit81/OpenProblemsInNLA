# KE-05 independent import-candidate review

**Approve the held 142-file candidate for a fresh committed Linux verification run. This approval concerns preservation, metadata, build configuration, evidence, and attribution. It does not claim that this candidate has already passed a fresh Lean or Comparator run.**

Reviewer: OpenAI Codex AI agent `/root/mf22_publication_referee`, 16 September 2026 UTC. I did not prepare the import or modify any source. The reviewed candidate manifest is `KE05-CAMPAIGN-CANDIDATE.json`, SHA-256 `47a08c76ff9ec6398d707db6210b944e60c2d836bb954b55a2bacdf7046a9d79`, rooted at `/private/tmp/nla-lean-next-ke05-worktree/randomized-and-low-rank-approximation/KE-05/lean`. The worktree is based on upstream `ce47b5630bf3680d9211131c3a43825b022c139a`; the project was untracked and no tracked change was present at inspection.

This is a continuation of my independent complete mathematical and historical-runtime review at `KE05-mf22-independent/REVIEW.md`, SHA-256 `ef6d2b6451b7b6099acc7e9603aa8290af74816074517ac256644657d4164752`. That review personally read all 23 Lean inputs and the complete original target, and audited actual historical run `34927150695`. The present audit independently proves that every one of those reviewed mathematical bytes is retained; it does not substitute metadata inspection for the earlier complete mathematical reading.

## Original-source and frozen-boundary preservation

I independently bound all 93 imported original files to Git blobs at Sidney Holden's published source `04f3f39beb69d77dbc4a8eadee70259eb89a591a`. All 90 protected original files are unchanged. Exactly three original files differ: README, formalization metadata, and the Lakefile. Each of their complete original versions is retained under `verification/campaign-import-2026-09-16/before/` and matches its original Git blob. All 142 current files match the supplied candidate manifest, with no symlinks or undeclared extra files.

All 23 mathematical files, including Definitions, Challenge, all proof modules, and Solution, match both the published revision and the actual historically tested revision `9acd5d5c9ab91c5c0c07603b6b48c0cb7ede54e6`. They also match the exact hashes from my prior full-source review. The ten frozen target declarations, mathematical definitions, numerical boundary, dependency manifest, Lean toolchain, and Comparator policy are unchanged. The permitted axiom set remains exactly `propext`, `Classical.choice`, and `Quot.sound`, with no replaceable definition holes.

I reconciled both Lakefile transitions. The original statement-time Lakefile plus the previously documented Solution-library registration reproduces the published pre-import Lakefile exactly. The current change replaces only `defaultTargets = ["Challenge"]` with `defaultTargets = ["Solution"]`. The Solution library was already registered. No dependency, option, library root, executable, or mathematical input is changed. This amendment fixes the developer command's default target while retaining the complete previous configuration and frozen history.

The permanent canonical README, problem registry, and resolved index remain unchanged. The candidate does not promote a catalog status, change a count, renumber an ID, or alter the original mathematical question.

## Metadata, credit, and reproduction

I read the entire new README and formalization.yaml, their changes from the retained originals, the full transition record, the review-retention map and explanatory README, the historical-evidence inventory, the labelled public run summary, and the retained preparation script. The README correctly describes the full negative answer, actual matrix recurrence, all root orderings, genuine Euclidean norms, independent standard-Gaussian law, and original uniform probability quantifiers. The fixed block-size-two, three-block family negates the universal conjecture. It is not presented as a scalar-only or empirical claim.

Sidney Holden remains the author of the existing Lean formalization in `project.authors`, source headers, README, and acknowledgements. Apache-2.0 is retained unchanged. George Stepaniants is credited separately for the mathematical proof, integration and verification submission, and current maintenance, with Department of Computing and Mathematical Sciences, California Institute of Technology. Nian Shao retains the framework and conjecture credit. The existing AI-assistance disclosures remain, and no human peer review, source-author endorsement, or transfer of mathematical/software authorship is implied.

The ten advertised result declarations and their axiom lists remain unchanged. Each result clearly identifies historical acceptance and says a fresh run is pending. `whole_problem_verified` is false for the current campaign candidate. The prose consistently separates the two new complete independent reviews from an actual new checker execution. It accurately describes LeanCert use as the ten compiled kernel trust assertions; it does not invent an interval certificate for this exact symbolic proof.

The actual v0.4 schema validates. I independently executed the repository metadata/Comparator-coverage validator, which returned `PASS (10 declarations)`. This command validates metadata and coverage only; it does not prove theorems. All 13 active relative Markdown links resolve, and every alignment path exists. The schema reference resolves to the intended shared schema. The current shared harness, workflow, and schema are unchanged from the historically tested source.

One nonblocking README clarification remains: its harness commands are relative to the repository root, while the immediately preceding developer `lake build Solution` command is explicitly run from the project directory. Adding “from the repository root” to the harness sentence would remove that working-directory ambiguity. The commands themselves and the selected Solution target are correct. This note is not a mathematical or execution blocker.

## Retained evidence and contact-field exclusion

All 19 copied campaign review records match their source packets exactly. The second packet's complete top-level manifest also validates in its retained location. The first packet's selection is explicitly described and enumerated; it is not misrepresented as a full copy of the larger private working directory.

All 20 retained historical evidence files match the previously authenticated historical directory byte for byte. This includes the exact artifact archive, raw job logs, result receipt, kernel/Comparator/sandbox/native/sorry controls, dependency log, and bootstrap logs. All 13 members inside the archive match the retained extracted files. The archive SHA-256 remains `6925d651c338b1ce7af48368af631e28e70a2cf047a5029db594b8aaae4da682`.

The original raw run API record embeds contact fields. It is not included in the candidate. Its SHA-256 is retained, and `run-public-summary.json` is plainly labelled a selection of identity/status fields rather than raw API bytes. Every selected field matches the private original: run ID, historical commit, branch, event, completion status, success conclusion, dates, and official URL. The omission is recorded explicitly; no source, checker log, receipt, or negative control has been rewritten to hide a failure or manufacture acceptance.

I scanned all 141 non-archive candidate files and every one of the 13 archive members for email-address patterns. There were no matches. This is a bounded content check on the complete supplied candidate, including its historical evidence and preparation script. No private raw commit-contact record is being published by this package.

## Remaining gate and review limits

This candidate is ready to commit and run through the actual shared non-root Linux harness. Before canonical promotion or counting, authenticate the fresh run on the committed candidate, bind every input, confirm all ten Comparator/default-kernel results and the required controls, and obtain the corresponding independent runtime review. The old run remains legitimate evidence for its own exact historical source and is not labelled as a fresh campaign rerun.

My executable audit only reads files, Git objects, metadata, and retained records. It writes this independent review packet. I executed no Lean, Lake, cache, or Comparator process, modified no author/candidate source, made no Git mutation, and performed no commit, push, publication, or count change. This is an independent AI-agent review under the repository's scoped protocol, not a certification of Lean itself or an official Tau Ceti service result.
