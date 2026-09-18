# Reproducing the exact degree-47 certificate

Run from the repository root with Python 3.9 or later; no third-party packages
or network access are needed:

```bash
python3 references/webb-mf14-degree47-2026-09-17/verification/verify.py
```

The runner checks the frozen input manifest, executes both final exact
checkers in an isolated temporary copy, and writes logs and results under
[`reproduction/`](reproduction/). It never executes or modifies the archived
[`source/`](../source/) in place. The input files are checked again after the
run. A successful run exits zero and prints `PASS`; an integrity, execution,
or certificate failure exits with status 2 and prints `FAIL`.

The certificate establishes an exact order-47 contact and an invertible
48-coordinate Jacobian. The [frozen proof](../source/proof.md) separately
justifies the actual seven-product chart, convergence in all 129 polynomial
coefficients, and the matching upper bound. The [independent final
review](../source/reviews/exact-degree47-final-review.md) audits those
mathematical implications. This is exact computer-assisted mathematics with
independent informal agent review, not proof-kernel verification or external
human peer review.

## Frozen inputs and provenance

[`input_manifest.json`](input_manifest.json) records the research-campaign
origin, repository baselines, byte sizes, and SHA-256 hashes of exactly ten
files. Its own SHA-256 is pinned in [`verify.py`](verify.py):

```
953116f9dd40f8c584a2f9cf1af840533c37ff9ced08f741ae901658f917d68b
```

The files were copied byte-for-byte from the completed 17 September 2026
campaign, preserving the relative `experiments/` and `reviews/` layout:

- Final `proof.md`, `TARGET.md`, and the source-bound final review.
- The frozen Gaussian-rational seed.
- The author's final degree-47 checker, its result, and its arithmetic helper.
- The independent full-degree-128 checker, its result, and its distinct
  arithmetic helper.

The helpers retain their original bytes, including earlier routines that the
final checkers do not call. Earlier seeds, searches, intermediate proofs, and
unrelated campaign material are excluded. The author checker uses forward
jets; the independent checker uses full polynomial values, reverse chain
rules, and a different uniform Hessian bound.

The runner rejects missing, extra, symlinked, or changed source files and a
changed manifest. It requires the regenerated author result to match its
frozen bytes. The independent result must match every archived field except
`elapsed_seconds`; the full degree-128 array digest and all mathematical
bounds must match exactly. The new runner also checks the exact contraction
and self-map inequalities with explicit exceptions rather than assertions.

## Assertions and optimized Python

The original checkers use Python assertions and are preserved without edits.
The runner refuses an interpreter started with `-O`, `-OO`, or an effective
`PYTHONOPTIMIZE` setting. It launches children with `-E -B -s`, checks their
interpreter flags, and never supplies an optimization flag. `-E` prevents
`PYTHONOPTIMIZE` and other Python environment settings from disabling child
assertions; `-B` prevents bytecode files in the isolated copy.

If the surrounding environment sets `PYTHONOPTIMIZE`, safely ignore that
setting for the runner itself:

```bash
python3 -E references/webb-mf14-degree47-2026-09-17/verification/verify.py
```

For example, the committed reproduction was run with
`PYTHONOPTIMIZE=1` present and `python3 -E`; its summary records that both
children ran with optimization level zero and ignored Python environment
variables. Direct optimized execution of a frozen checker is not an accepted
reproduction command.

## Fail-closed controls

Run the integration controls:

```bash
python3 references/webb-mf14-degree47-2026-09-17/verification/test_verifier.py
```

Eight tests cover unchanged inputs, a changed rational seed, a changed
manifest, an unlisted source file, a source symlink, `-O` and `-OO`, an
optimization environment variable, and safe use of `-E`. Mutations are made
only in temporary package copies. Negative controls require a nonzero exit,
an explicit failure reason, no `PASS`, and no reproduction directory.

A quick integrity-only check is also available:

```bash
python3 references/webb-mf14-degree47-2026-09-17/verification/verify.py --check-inputs-only
```

Use `--output-dir PATH` to place newly generated logs elsewhere. The runner
refuses an output directory inside frozen `source/`.

## Recorded reproduction

The relocated package passed on Python 3.14.0 on 17 September 2026:

- [Runner log](reproduction.log).
- [Machine-readable summary](reproduction/summary.json).
- [Author checker log](reproduction/author-checker.log) and
  [regenerated exact result](reproduction/author-result.json).
- [Independent checker log](reproduction/independent-checker.log) and
  [regenerated result](reproduction/independent-result.json).
- [Eight passing fail-closed controls](fail-closed-tests.log).

Generated runtime metadata and temporary paths may vary. Frozen source bytes,
exact bounds, and the digest of the reconstructed full coefficient arrays are
required to remain identical.
