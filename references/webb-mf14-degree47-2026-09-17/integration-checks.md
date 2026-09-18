# Local contribution checks — 17 September 2026

Prepared on branch `codex/mf14-degree47-resolution`, based on upstream `main`
commit `15b755d2` (the earlier degree-44 PR #287 was already merged).
The user requested that this contribution remain ready locally. No push or
pull request was made for this degree-47 contribution.

## Exact certificate and package

Both frozen exact degree-47 checkers reproduced successfully in the relocated
package. The author certificate is byte-identical to the archived result;
the independently reconstructed full degree-128 certificate matches every
mathematical field and digest, excluding elapsed-time metadata. All ten frozen
source files match the original campaign bytes and pinned input manifest.
The packaging reviewer also reran the checks independently.

```sh
python3 -B references/webb-mf14-degree47-2026-09-17/verification/verify.py
python3 -B references/webb-mf14-degree47-2026-09-17/verification/test_verifier.py
```

The eight rejection controls pass. The package preparer additionally reproduced
the full result with `PYTHONOPTIMIZE=1` present while starting the parent with
`python3 -E`: the recorded child flags show optimization disabled and Python
environment options ignored. Plain optimized invocations are explicitly refused.
See [verification documentation](verification/README.md),
[exact rerun summary](verification/reproduction/summary.json),
[rejection-control log](verification/fail-closed-tests.log), and
[contribution review](verification/packaging-review.md).

## Repository checks

All of the following completed successfully from the contribution worktree:

```sh
python3 tools/format_math.py --write MF-14
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 tools/render_problems.py MF-14
python3 tools/format_math.py --check
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 -m unittest discover -s tests -p 'test_problem_statuses.py' -v
python3 -m unittest discover -s tests -p 'test_format_math.py' -v
python3 -m unittest discover -s tests -p 'test_render_math.py' -v
```

Results: 217 permanent IDs validated; 17 ID tests, 3 status/count tests,
16 formatting tests and 11 rendering tests passed. No canonical description
needed mathematics-format repair. Index regeneration preserved the counts:
50 Lean verified, 42 Open, 70 Partially resolved, 55 Solved.

The original MF-14 problem-statement section and the attributed Colbrook
section are byte-identical to upstream `main`. The ID registry, category index,
main README and catalog are unchanged. The prior Webb degree-44 and Colbrook
reference archives have no changes. The new resolution adds the exact maximum
without changing the retained original equality or the `Solved` status.

## Documents

The standalone manuscript was compiled with XeLaTeX twice, with no reported
warnings, overfull/underfull boxes, missing references or missing citations.
Its six pages were rendered and visually inspected. The regenerated canonical
entry also reports a clean build; all three pages were visually inspected.
No clipped text, missing mathematical symbols or overlapping content was found.
The complete original question remains together on the entry's third page.
The packaging reviewer separately compared the manuscript mathematics with the
frozen proof and checked the exact parameter ordering and certificate constants.

The executable checks establish finite exact arithmetic. The membership,
contraction existence, inverse-function limit and dimension upper bound have
separate mathematical review. This record does not claim proof-kernel checking,
external human peer review or CI execution on GitHub.
