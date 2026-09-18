# Permanent problem numbering

The maintainer requires every published problem number to remain unchanged forever.
Never renumber, compact, recycle, or reassign an existing ID, including after a
solution, withdrawal, or category-listing change. Preserve its canonical README
path and original mathematical target. Keep solved or withdrawn entries as
retained pages; changing the open-problem count does not change any ID.

`problem_ids.json` is the append-only ID-to-canonical-README registry. For a new
entry, choose the next number above every registered number with that prefix
(for example, `RA-18` after `RA-17`), and explicitly add its ID/path pair to the
JSON object. Never fill gaps. Use at least two digits (`RA-01`, `RA-100`).

Before regenerating indexes, validate against the branch's published base:

```bash
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
```

The validator also runs automatically before index generation and in CI. It
checks identity and paths; review still must ensure an existing page's target
has not been replaced by an unrelated problem. Do not weaken the safeguards to
make a numbering change pass.

# Lean verification workflow — user instructions, 16 September 2026

Continue formalizing all remaining solved canonical problems, using multiple
agents on different proofs and independent reviews. Submit a separate pull
request for each completed problem to `ajt60gaibb/OpenProblemsInNLA:main`.

Develop and test Lean proofs locally before pushing them. Do not use GitHub
Actions as the iterative compiler/debugging loop: local failures should be
fixed locally to avoid wasted runner time and failed-run emails. Keep at most
one local Lean compiler process, with one thread and a 4096 MiB limit, while
agents work in parallel on sources and reviews. Reuse only pinned caches and
source-matched successful outputs.

Use GitHub's non-root Linux runner for the final real Comparator/kernel/sandbox
checks. The user explicitly confirmed this division of work. Distinguish actual
local Lean runs from GitHub Comparator runs in every verification claim; retain
the exact source hashes, commands, logs, run IDs and reviewer scopes. Never
report an unrun check as successful. Avoid redundant all-project workflows when
creating branches; check which projects the workflow actually selected.

Preserve statement-first development, kernel-mode LeanCert, computation
minimization, independent statement and proof reviews, the pinned Tau Ceti
review guidance, exact Comparator contracts, and truthful `formalization.yaml`.
Count complete distinct original targets only. Credit George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, for his contribution, preserve prior mathematical/code authorship,
and do not publish his email.

Reconfirmed by the user on 17 September 2026: Comparator runs on GitHub;
there is no requirement to find or install a local Comparator. Run Lean
development and tests locally before publication, and keep multiple agents
working on different proofs and independent reviews. Parallel agent work must
not create parallel local Lean compiler processes. Preserve this workflow
across resumed sessions and record local and GitHub results separately.
