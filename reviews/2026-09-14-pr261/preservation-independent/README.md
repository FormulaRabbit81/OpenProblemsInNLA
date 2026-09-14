# Independent PR261 preservation cross-check

**PASS within this bounded scope.** This separately authored, read-only check compares published base `27540c8022a33fef171625b7e48a95e33562d535` with submitted source `9bf50028bc30e6cdf78e19089befcb9b9bd6c292`. It reads their immutable Git objects and does not import the maintainer's checker, repository tools, or submitted code. It makes no remote changes.

All **217** registered IDs and canonical paths remain identical. **211** canonical READMEs are byte-for-byte unchanged. For AC-01 through AC-06, removing only the appended research notice and restoring the last-checked date recovers the entire prior README text, apart from terminal blank lines. Thus every original target, qualification, prior citation, rating, and status remains present. Titles and difficulty, importance, rating rationale, topic, and status fields were also compared directly, preserving absent optional fields. All six AC entries remain **Open**.

No previously tracked file is deleted, renamed, or changed in mode or type. Exactly **19** existing files change: the six canonical READMEs, their six TeX sources and six PDFs, plus `RESOLVED.md`. All **262** additions are under `references/holden-ac-2026-09-14/`. Each changed TeX source retains every prior non-whitespace character after removing the appended notice and restoring its literature-check date. The AC-02 and AC-04 diffs additionally rewrap existing mathematical text without changing it. `RESOLVED.md` retains its complete prior bytes around one six-line insertion explicitly stating that all six remain Open.

The registry, `CATALOG.md`, root README, and every category README have identical Git objects. Counts and rating distributions therefore remain unchanged, and a separate parse of all 217 canonical pages confirms these literal status counts: **42 Open, 72 Partially resolved, 72 Solved, 31 Lean verified**. This is a preservation check, not a fresh literature assessment of those statuses.

All **227** submitted member byte streams have independently recomputed SHA-256 digests matching the committed provenance manifest. Its member path set exactly equals the submitted subtree: no recorded member is missing and no submitted file is unrecorded. Package counts are AC-01: **27**, AC-02: **51**, AC-03: **15**, AC-04: **75**, AC-05: **21**, and AC-06: **38**. The detailed JSON records each actual digest and byte length.

The **six original top-level ZIP files are unavailable** in the source tree. Their declared archive hashes are retained in the JSON but were not independently authenticated; extraction completeness cannot be compared with their original central directories. The five included nested ZIPs were hashed as intact member files, without re-extraction. Matching a committed manifest establishes consistency, not author identity, original archive authenticity, or mathematical validity.

This cross-check intentionally does not repeat mathematical reasoning, supplied checkers, PDF visual review, repository tests, or external-source research. Those belong to the separate pairwise audit reports. It does not infer semantic PDF preservation from binary changes.

## Evidence and reproduction

- [`preservation.json`](preservation.json): exact refs and trees, scope checks, unchanged index objects, six changed-page comparisons, all 227 member hashes, and explicit limitations.
- [`check_preservation.py`](check_preservation.py): independently written Python standard-library checker, using only read-only Git commands. Failed invariants raise errors, so checks remain active with Python optimization.
- [`SHA256SUMS`](SHA256SUMS): hashes of this report, checker, and result JSON.

From a checkout containing both exact commits, reproduce without network access:

```sh
python3 check_preservation.py --repo /path/to/OpenProblemsInNLA --output /tmp/pr261-preservation-recheck.json
```

The successful original run used `/private/tmp/nla-audit-261` and wrote this result JSON. The checker output reported 217 preserved canonical pages, zero deletions, 19 modified existing files, 262 additions, and all 227 matching member hashes. No assertion-only checks are used.
