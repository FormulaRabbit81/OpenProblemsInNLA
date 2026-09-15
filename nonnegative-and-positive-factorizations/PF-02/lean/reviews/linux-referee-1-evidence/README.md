# PF-02 independent Linux referee 1 evidence

This archive records an independent operational audit of GitHub Actions run
35021020857, attempt 1, target job 104556550871, proof commit
`a3e984ced348f4d8529c5d0f8f87c9be7dd979e2`. The reviewer implemented no proof.

The three `github-*.json` files were independently queried through `gh api`:

- `repos/ajt60gaibb/OpenProblemsInNLA/actions/artifacts/10418540042`
- `repos/ajt60gaibb/OpenProblemsInNLA/actions/runs/35021020857`
- `repos/ajt60gaibb/OpenProblemsInNLA/actions/jobs/104556550871`

Run and job responses retain the fields relevant to this audit. The actual
original ZIP, its complete extracted contents and original provenance remain
in `../../verification/linux-2026-09-15/`. The independently queried artifact
digest authenticates all 13 extracted file members.

`audit.py` checks these files at the original absolute local paths, all 70
receipt inputs against current files and proof-commit Git objects, the pre-proof
freeze and complete source approval inputs, all 58 locked checker sources,
actual invocation/environment, and the control outputs. Its 389 assertions
passed. `audit.json` records every check and all underlying evidence hashes.
The reviewer also read the 12 actual logs and relevant source manually.

This is an audit of that actual hosted Linux run. It is not a second local
Linux run or a claim of rebuilding Linux binaries on the reviewer's macOS host.
Run `shasum -a 256 -c SHA256SUMS` here to validate this audit archive.
