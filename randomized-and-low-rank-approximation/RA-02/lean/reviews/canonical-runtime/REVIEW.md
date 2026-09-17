# RA-02 canonical Linux runtime evidence review

**APPROVED for literal proof commit `26dc080e47b75a3aaf2e75fc2a282d0b8f4a4bbb`.**
The retained actual GitHub run completes the default-kernel replay, all 27
Comparator contracts, and the required rejection and sandbox controls.
This approval covers execution evidence for that commit. It is not a fresh
execution, a new complete mathematical source review, or acceptance of an
unrun publication or upstream merge checkout.

Reviewer: `/root/sf_ra_runtime_referee`, nonauthor of these statements, proof
sources, packages and execution harness. I read the full 12 artifact logs and
independently ran the attached read-only Python evidence audit. The previous
agent supplied the authenticated GitHub retrieval; I did not claim a new remote
fetch. No official Tau Ceti endorsement, human review, or machine independence
between agents is implied.

The execution is [GitHub run 35175272827](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35175272827),
attempt 1, verify job `105055587640`. It succeeded on the fork
`sgstepaniants/OpenProblemsInNLA`. The API head, receipt and literal checkout in
the raw job log all match the commit above. This was a push execution. The
actual selector selected only RA-02. Artifact `10477794322` has SHA-256
`a475b2aeecd1d6224ad1b33aa6915858578a4ef6748a3f9f62eb8513fbf5134c`;
the retained ZIP, API artifact digest and raw upload log agree.

The attached audit completed successfully with **973 assertions and 293
external file bindings**. Its exact executed command is
`python3 /tmp/nla-lean-next-20260915/reviews/RA02-runtime-referee-35175272827/audit.py`.
`AUDIT.log` contains its direct stdout/stderr; `AUDIT-EXECUTION.json` records
argv, timestamps, script/log hashes and exit zero. `ASSERTIONS.json`,
`CHECKS.json`, `GIT-INPUTS.json` and `SOURCE-BINDINGS.json` retain the results
and source bindings.

- All 220 tracked project inputs match their literal Git blobs, receipt hashes
  and inspected worktree bytes. All 35 accepted source files match their
  previously accepted local source origins and both complete nonauthor source
  referees' maps. The first review's `Complete.lean` entry is transported to
  `Solution.lean` with identical bytes; the second map already uses Solution.
  Both full review manifests and all their payloads remain exact. This is a
  byte-continuation check, not a replacement for those reviews or their scopes.
- All nine original frozen inputs are retained exactly. Eight active inputs,
  including Definitions, Challenge, Comparator contracts and pins, are unchanged.
  The sole active frozen configuration transition selects and registers the
  Solution library in Lake. The original Lake snapshot is intact. The canonical
  wrapper has an ordered axiom report and explicit kernel-trust assertion for
  every one of the 27 frozen exports.
- The shared checker and workflow equal accepted commit
  `ff6abf718126ceb23f933cf4f627f95104461fe8`. The source-lock digest is
  `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`.
  The receipt records Linux, Lean 4.33.1, pinned Forsythe revision
  `8d1b0c0545a77b40245e84705aa7d273e6c81e62`, and checker/exporter/Landrun
  executable hashes. All ten exact dependency revisions appear in the actual
  dependency log and equal the committed manifest and local acceptance pins.
- The actual log builds every one of the 34 NLA modules in the independently
  reconstructed final import closure and the canonical Solution wrapper.
  Challenge has exactly its 27 intentional specification holes. Solution and
  its final imports have no admitted-proof diagnostic. Both exported theorem
  lists match the configured ordered 27 names. Every Solution axiom report
  contains exactly `propext`, `Classical.choice` and `Quot.sound`.
  Default-kernel replay accepts the solution, then Comparator reports acceptance.
  The observed deprecated syntax, unused-simp/tactic/variable and proof-style
  warnings do not hide a compiler failure or forbidden axiom.
- The unchanged explicit kernel-mode LeanCert certificate for `exp(1) <= 3`
  is consumed by the rank denominator bound, then by the exponential tail
  factor and final counterexample. This is a source-continuation and runtime
  trust check, not a new full mathematical review.
- The `sorryAx` and `native_decide` fixtures actually fail with the required
  forbidden-axiom diagnostics. All three builtin-kernel controls pass, including
  rejection of the invalid raw proof and quotient post-check mismatch. All five
  Comparator regressions pass with their specified phases and exit codes.
- Build and export sandbox probes both run as UID 1001, with no effective
  capabilities, `no_new_privs`, private user/PID/mount/network/IPC/UTS namespaces,
  denied host-process access and network/AF_UNIX access, and denied writes outside
  the authorized area. Build may write its designated `.lake` fixture; export
  cannot. Nested namespace writes and all four invalid argument cases are
  rejected. The user-service probe succeeds, and fixture post-checks pass.
- Every artifact log's complete payload equals its contiguous raw job-log block
  after the documented timestamp/ANSI/blank-line/header/footer normalization.
  All 13 ZIP members equal the extracted bytes. The standalone `checker-controls`
  job was skipped on this unchanged-harness push; the required per-proof
  controls above actually ran inside the successful verify job.

The pinned Tau Ceti review guidance and correctness, generality, proof-quality,
reuse and attribution rubrics, and Comparator README are byte-identical to
those I read during the immediately preceding SF-01 audit. All nine retained
standards snapshots were rechecked against its sealed literal-source map.
Kernel acceptance does not certify informal mathematical fidelity; that remains
the scope of the separate statement and full source reviews. I read both final
RA-02 source-review reports and checked their preserved manifests and source
maps without expanding their claims into a new full-source review by me.

The prior generic `ROOT-AUDIT.json` is retained and hash-bound as corroboration.
Its helper has a hardcoded `/root` reviewer label. I did not rerun that helper.
The coordinator separately reported executing that helper again as `/root`
during this task, with unchanged `ROOT-AUDIT.json` bytes; that root invocation
is distinct from my audit. The attached audit independently reconstructs the
relevant evidence checks and adds full raw-log/ZIP correspondence and both
source-review continuation maps.

No Lean, Lake, Comparator, cache or compiler was run by this reviewer. Git was
used only to read immutable objects and compare files. No proof/worktree, Git
state, workflow, publication, PR or count was changed. This report preserves
the separately recorded mathematical/code authorship and George Stepaniants's
Department of Computing and Mathematical Sciences, California Institute of
Technology credit, and publishes no personal contact address. A later
publication commit and upstream merge checkout require their applicable exact
source and runtime checks.
