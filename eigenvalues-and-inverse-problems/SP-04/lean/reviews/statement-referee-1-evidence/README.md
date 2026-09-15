# SP-04 independent statement referee 1 evidence

This evidence covers the exact pre-proof boundary. It does not contain proof
implementation, a proof kernel/axiom audit, or an authoritative Comparator run.

A fresh source snapshot was created at `/private/tmp/nla-sp04-statement-referee1`
without copying project build artifacts. Pinned dependency caches were reused
after checking all ten Git revisions and tracked-file cleanliness. With the
pinned Lean 4.33.1 Darwin arm64 compiler directory prepended to PATH:

```sh
lake build Challenge
lake env lean AuditBoundary.lean
python3 independent-arithmetic.py
python3 seal-evidence.py
```

All four commands exited zero. Challenge has eleven intentional specification
holes and proves no target. AuditBoundary only prints definitions/types and
checks available API signatures and instances; it implements no theorem.

The independent arithmetic script uses only Python's standard library and
writes its adjacent JSON output. It was written and run before reading the
author's checker and neither imports nor executes it. Its different exact
stationary sample uses t=2487/5000. The 49 arithmetic checks are diagnostic
evidence, not a substitute for the future universal Lean proofs.

`execution-record.json` contains all ten boundary hashes, four complete
original-source hashes, the independently recovered historical proof-block
hash, dependency revisions, API-file hashes and actual execution results.
`seal-evidence.py` documents the final checks at the original absolute scratch
paths. All four original sources were also checked against the published base.

Run `shasum -a 256 -c SHA256SUMS` here to validate this retained archive.
