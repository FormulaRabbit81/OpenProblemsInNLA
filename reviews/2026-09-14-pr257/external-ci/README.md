# PR257 external Lean CI authentication

**Verdict: PASS for external verification authenticity.** Reviewed on 2026-09-14
for PR257 head `cc661b4170e590daeb2ca4232336ab8b6d2eeaaf`. The independent external
run really checked formal source commit
`762bd5ec5050a96f5e6ba3926b6cda4816fcd4b0` and theorem `MI32.main_upper`.
No substantive external CI evidence gap was found. This report does not replace
the separate mathematical statement-fidelity review and does not claim a local
Lean, Comparator, or NanoDa rerun.

## Evidence authenticated

- GitHub API records show [run 34852526384](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34852526384)
  succeeded on attempt 1, using PalomarSubmission workflow commit
  `a013555a88a0fc9ec910a09ea833dc9cc338db35`. All required build, replay, upload,
  and final verification-status steps succeeded; this was full verification,
  not merely preflight.
- Downloaded artifact 10352481140 has SHA256
  `f41da54a78dad5851171c11450c2acae33acc615279a68770a11c89239e27955`, exactly
  matching GitHub's artifact digest. The original ZIP and original GitHub run-log
  ZIP are retained. The decoded mechanical report records `status: pass`,
  `stage: complete`, no errors, and the exact source revision above.
- The selected configuration has only theorem `MI32.main_upper`,
  `definition_names: []`, and permitted axioms `propext`, `Quot.sound`,
  `Classical.choice`. Its actual Comparator log reports both “nanoda kernel
  accepts the solution” and “Lean default kernel accepts the solution”, followed
  by “Your solution is okay!”. This is stronger evidence than a green job badge
  or the author's submitted axiom log alone.
- The [versioned registry record](https://data.palomar-registry.org/entries/PALOMAR-2026-09-14-000006-v1.json)
  for `PALOMAR-2026-09-14-000006`, version 1, is registered with trust level
  `high`. Its preserved mechanical report is byte-for-byte identical to the
  GitHub artifact, with SHA256
  `90674b1635e8b029e362827423bdc52941c8a65e7e5f775db7d49169951ae2ad`.
  Its receipt and editorial-report hashes also match the downloaded files.
- Challenge, Solution, Comparator configuration, Lakefile, dependency manifest,
  formalization metadata, and license hashes match the immutable public source.
  Lean is `leanprover/lean4:v4.33.0`; all nine dependency revisions match the
  mechanical report, including mathlib
  `db584cd6d46c92f209a44c0f1c829460d327499d`.
- The original repository and the independent
  [Palomar archival fork](https://github.com/PalomarArchive/DiarHaidary--Spectral-norms-of-independent-entries-with-regular-moment-growth--b1249e53599c/tree/762bd5ec5050a96f5e6ba3926b6cda4816fcd4b0)
  both report the same commit and Git tree
  `8db1a2a4ad74de0675213099aefbf3fe4a5544ca`. The preserved version tag points
  to that exact commit. Independently downloaded tarball payloads agree for all
  196 regular files, whose two SHA256 inventories are retained. No source
  tarball or full source tree is included in this evidence bundle.

## What the verification actually enforces

Read the [exact workflow](https://github.com/PalomarRegistry/PalomarSubmission/blob/a013555a88a0fc9ec910a09ea833dc9cc338db35/.github/workflows/submission.yml)
and relevant source-fetch, configuration, sandbox, canonical-Challenge,
execution, and status-handling paths in the
[pinned verifier implementation](https://github.com/PalomarRegistry/PalomarSubmission/blob/a013555a88a0fc9ec910a09ea833dc9cc338db35/scripts/verify_submission.py).
The fetch verifies the requested commit. The verifier rejects excess permitted
axioms, forces NanoDa in its protected configuration, compiles the canonical
Challenge directly against frozen allowlisted dependencies, and publishes it
under an unpredictable protected module alias. Submitted Lake configuration
does not compile that canonical Challenge. The candidate cannot write the
protected challenge, verifier tools, or report; confinement has positive and
negative controls, and protected tools/artifacts are hash checked. A pass
requires Comparator's zero exit status and survives a final report-status gate.

Read the relevant upstream Comparator source at
`575674928e239f5bc452aab72d1dd7b0f1326494` (retained here). It compares selected
theorem types and their definition dependencies against the Challenge; with no
definition holes, those definitions cannot be replaced. Its axiom check walks
the selected solution's dependency closure and requires an actual theorem. It
replays the exported solution through NanoDa with unpermitted axioms treated as
hard errors, then through Lean's default kernel, and rejects either failure.
Thus the allowed-axiom list is enforced, not just reported. The complete exact
list printed by `#print axioms` is also present in the submitted source log, but
that submitted log is not an independently executed axiom enumeration in this
audit; the external replay establishes containment in the standard allowlist.

Actual GitHub logs and the mechanical report agree on these pins:

| Tool | Revision |
| --- | --- |
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| lean4export | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

This was a bounded review of the relevant verification path, not a complete
security audit of every pipeline component or an independent verification of
the kernel implementations themselves. It relies on the official GitHub run
and pinned upstream verification tools. No submitted project code was executed
as part of this authentication subtask.

## Limits and reproduction

Palomar's editorial outcome is `neutral`, with a warning about an inaccurate
informal description of the LocalLogMoment companion result. The registry
retains that warning at the verified source revision. Its editorial assessment
is AI generated; registration/high trust is not a human referee report,
endorsement, or novelty determination. The later manuscript revision is outside
this external-run authentication. Only `MI32.main_upper` is the selected kernel
target; other companion theorems and the fair-sign nonvacuity witness are not
separately selected by this Comparator run.

From this directory, using Python's standard library only:

```sh
python3 check_authenticity.py
python3 -O check_authenticity.py
```

To recheck every recorded source-file payload against a separately obtained
checkout of the exact formal revision:

```sh
python3 check_authenticity.py --source-tree /path/to/exact/checkout
```

Both normal and optimized Python checks passed, and all 196 source payloads were
checked against the independently downloaded source tree. Checks use explicit
exceptions rather than Python assertions. The script checks consistency of
preserved evidence, not mathematical truth or fresh remote state. Original
download locations are recorded in `SOURCES.json`; `SHA256SUMS` inventories
the retained bundle. GitHub's original artifact expiry is 2026-12-13, which is
why its small original ZIP is preserved here alongside the registry copy.
