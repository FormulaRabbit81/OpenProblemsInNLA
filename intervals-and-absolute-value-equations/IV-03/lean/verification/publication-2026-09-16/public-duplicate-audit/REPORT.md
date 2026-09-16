# Remaining solved-problem public Lean coverage

Reviewer: OpenAI Codex agent `/root/mi04_independent_referee`. This is a bounded duplicate-work audit, not proof acceptance. No Lean/Lake, new proof implementation, status change, publication or verified-count increase occurred.

**One additional full-target candidate was found: IV-03.** It is on `sidneyholden1/OpenProblemsInNLA`, branch `codex/lean-iv03`, immutable head `281f440650d174602120ca9b2b930d38f9fef205`. It warrants independent full-source and actual-evidence review before anyone starts a duplicate implementation. KE-05 was excluded because its existing formalization is already under review.

## Exhaustive map within the retained public snapshot

`COVERAGE.json` contains one record for each of the 59 eligible canonical IDs, including exact canonical README path, canonical snapshot hash, repository/branch/head SHA for every match, and every active, historical/review-only or noncanonical candidate path. `TREE-CHECKS.json` records all 203 complete immutable trees representing 249 public branch heads in 14 repositories. Every retained compressed file and decompressed response/path-list hash was checked against the earlier audit manifest and scan record. All trees were nontruncated or complete tracked-path listings.

The public snapshot was collected at 2026-09-16T04:04:30.936969Z. The campaign snapshot used here is retained. Exclusions are explicit: 31 baseline verified IDs; accepted own submissions MF-02, MF-24, IE-04, MF-12 and IE-14; accepted overlaps IE-15, IE-17, PF-02, SP-04 and SP-05; current own candidates MF-22, MI-04 and IE-13; and KE-05 already under review. That leaves 59 targets from the original 104-problem campaign snapshot.

The scan includes `.lean`, historical `.lean.txt`, and `formalization.yaml`/`.yml` paths, recognizing canonical IDs with or without hyphens and with ordinary zero-padding. It found a target-named source footprint for IV-03 alone. There are no historical-only, helper-only or noncanonical-only hits for the other 58 eligible IDs in these trees. Seven paths without any problem ID were inspected by path: one archived Forsythe reproduction probe and six archived Mathlib primary-source files. They are not independent remaining-problem formalizations. Their exact paths and associated commits are retained in `UNNAMED-LEAN-PATHS.json`. The supplemental title scan of 149 upstream PR records found no Lean/formalization-titled PR naming an eligible remaining ID; it is not an exhaustive PR-body audit.

This is a bounded absence finding. It does not exclude private, deleted, unpushed, later, unusually named or otherwise undiscovered formalizations. No green badge, README assertion or copied evidence file is treated as runtime acceptance.

## IV-03 candidate triage

| Item | Finding |
|---|---|
| Repository | `sidneyholden1/OpenProblemsInNLA` |
| Branch | `codex/lean-iv03` |
| Head | `281f440650d174602120ca9b2b930d38f9fef205` |
| Canonical active root | `intervals-and-absolute-value-equations/IV-03/lean/` |
| Active footprint | 14 Lean files, including Challenge and Solution, plus formalization.yaml |
| Other footprint | 22 historical/review/evidence Lean paths; zero noncanonical candidates |
| Formalization author | Sidney Holden |
| Mathematical author | Matthew J. Colbrook |
| License | Apache-2.0 |
| Triage classification | Complete-target candidate; neither a helper-only nor historical-only project |

The exact project is browsable at [the immutable IV-03 source](https://github.com/sidneyholden1/OpenProblemsInNLA/tree/281f440650d174602120ca9b2b930d38f9fef205/intervals-and-absolute-value-equations/IV-03/lean). Its active paths are Challenge.lean, Solution.lean, and the NLA/IV03 modules Definitions, Proof, Principal, Complementary, Adjugate, Cofactor, Monotonicity, SchurInterval, IntervalStructure, IntervalAdjugate, IntervalInduction and Vertices. Every path and available Git blob ID is in the coverage map.

I fetched and read fourteen small files at that exact commit: the canonical README, project README, manifest, Challenge, Definitions, Proof, Solution, license identification, source provenance, numerical targets, proof notes, Comparator configuration, toolchain and lakefile. Each downloaded file's actual Git blob hash was checked against the retained immutable recursive tree; SHA-256 hashes and URLs are in `IV03-SOURCE-FETCH.json`. I independently obtained the upstream canonical README at `ce47b5630bf3680d9211131c3a43825b022c139a` using read-only Git. Its original problem-statement section is byte-for-byte identical to the candidate branch's retained problem statement.

The four Challenge contracts include the true full equivalence: for every positive dimension and all real ordered closed entrywise intervals, every matrix is inverse M if and only if all n-squared negative-sign vertices are inverse M. The full original two-sign criterion is then also an export. Definitions guards invertibility with `IsUnit A`, requires actual entrywise nonnegativity, and requires nonpositive off-diagonal entries of the actual inverse. Thus a singular totalized inverse cannot satisfy the predicate accidentally. Ordered endpoints and positive dimension are the only extra outer premises; there is no interval regularity assumption, no real-to-complex change, no strict-width requirement and no fixed-dimensional restriction.

Solution exposes exactly the four declared targets and imports the actual interval-induction module. Its kernel trust requests and axiom-print commands are present. The proof notes describe all-dimensional induction through genuine principal/Schur closure, adjugate completion without assumed invertibility, and exact resolvent box comparisons. The inspected foundational Proof module implements maximum-principle and determinant-sign arguments rather than assuming the main criterion. This is enough to classify the candidate's intended scope, but I have not read the other ten proof modules or certified their correctness in this triage.

The README and manifest claim source-bound Linux/Comparator success at proof revision `516ad4a0e85c21c7ef34507db9ab3b68b393bb90` and [run 34926260380](https://github.com/sidneyholden1/OpenProblemsInNLA/actions/runs/34926260380). **These are retained author claims, not independently authenticated results of this task.** Before counting or incorporating the work, inspect the complete proof closure and both referee reports, retrieve the actual GitHub run/artifact and controls, compare every tested input with its commit, and verify that the published branch's active proof bytes match the accepted proof revision. Preserve Sidney Holden's formalization authorship and Apache license, and Colbrook's mathematical credit; do not substitute George Stepaniants as author of this existing development.

## IDs with no target-named Lean/manifest hit

AA-01; AV-01, AV-02; IE-02, IE-08, IE-10, IE-12, IE-21, IE-22, IE-26; IV-02, IV-04, IV-05; KE-03; MD-03, MD-04, MD-06; MF-03, MF-05, MF-06, MF-07, MF-18, MF-21; MI-13, MI-16, MI-24, MI-27, MI-28; NM-03, NM-04, NR-04; PF-03, PF-04, PF-05; RA-02, RA-04, RA-05, RA-10, RA-12, RA-13, RA-19; RE-05, RE-06; SF-01; SP-11, SP-12, SP-13, SP-15; TR-04, TR-06, TR-07, TR-08, TR-13, TR-14, TR-17, TR-20, TR-26, TR-27.

The practical next action is to review the existing IV-03 project after the already active KE-05 review. The remaining entries have no matching public source footprint within this snapshot and remain eligible for fresh implementation after an appropriate refreshed preflight.
