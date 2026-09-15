# PF-02 independent final referee 1 evidence

These files record a fresh local source-snapshot review of commit
`61561dd99c57c7334b3304fa0ad88a51eeac84f2`. No project build cache was copied.
Pinned dependency caches were reused after checking all ten Git revisions and
tracked-file cleanliness. No isolated Linux or Comparator run is claimed.

The actual commands, with the pinned Lean 4.33.1 Darwin arm64 bin directory
prepended to PATH, were:

```sh
lake build Challenge
lake build Solution
lake env lean AuditFull.lean
```

The independent snapshot was `/private/tmp/nla-pf02-final-referee1`. The three
commands exited 0; full stdout/stderr is retained in the corresponding logs.
`AuditFull.lean` assigns the nine exact frozen Challenge types to the actual
exports, then checks 32 transitive closures for kernel trust and permitted axioms.

The metadata command was run from the repository root using the existing audit
Python environment with the repository requirements installed:

```sh
python tools/lean/validate_manifest.py nonnegative-and-positive-factorizations/PF-02/lean
```

`referee1-arithmetic.py` is this reviewer's independent, standard-library-only
exact arithmetic diagnostic. Running `python3 referee1-arithmetic.py` writes
its adjacent JSON record. It passed 48 assertions including the full nine-variable
congruence polynomial. It is supporting evidence, not a replacement for Lean.

`seal-evidence.py` records the final checks against the original local snapshot,
current source and candidate Git objects. Its absolute scratch paths describe
the actual execution location. `snapshot-inputs.json` seals all source bytes;
`execution-record.json` records results and the checked API-file hashes.

Use `shasum -a 256 -c SHA256SUMS` here to validate this archive.
