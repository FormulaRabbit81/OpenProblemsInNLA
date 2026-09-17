# SF-01 canonical Linux runtime evidence review

**APPROVED for literal proof commit `3312b0795873cfecade03fa421a5433651d47674`.**
The retained actual GitHub run completes the default-kernel replay, all 24
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

The execution is [GitHub run 35175258802](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35175258802),
attempt 1, verify job `105055517720`. It succeeded on the fork
`sgstepaniants/OpenProblemsInNLA`. The API head, receipt and literal checkout in
the raw job log all match the commit above. This was a push execution. The
actual selector selected only SF-01. Artifact `10478074528` has SHA-256
`3a459ec19dfdf960f4f0ec8e30f7ec249498b4b8f3a596b22be7783038e699c0`;
the retained ZIP, API artifact digest and raw upload log agree.

The attached audit completed successfully with **1,145 assertions and 344
external file bindings**. Its exact executed command is
`python3 /tmp/nla-lean-next-20260915/reviews/SF01-runtime-referee-35175258802/audit.py`.
`AUDIT.log`, `AUDIT-EXECUTION.json`, `ASSERTIONS.json`, `CHECKS.json`, `GIT-INPUTS.json` and
`SOURCE-BINDINGS.json` retain the results and source bindings.

- All 271 tracked project inputs match their literal Git blobs, receipt hashes
  and inspected worktree bytes. All 37 accepted source files match their
  previously accepted local source origins and the complete nonauthor source
  referee's source map. This is a byte-continuation check, not a replacement for
  the separate source reviews or their authorship disclosures.
- All nine original frozen inputs are retained exactly. Eight active inputs,
  including Definitions, Challenge, Comparator contracts and pins, are unchanged.
  The only active frozen configuration transition selects the existing Solution
  library as Lake's default instead of Challenge. The original Lake snapshot is
  intact. The canonical wrapper contains an ordered axiom report and explicit
  kernel-trust assertion for each of the 24 frozen exports.
- The shared checker and workflow equal accepted commit
  `ff6abf718126ceb23f933cf4f627f95104461fe8`. The source-lock digest is
  `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`.
  The execution receipt records Linux, Lean 4.33.1, pinned Forsythe revision
  `8d1b0c0545a77b40245e84705aa7d273e6c81e62`, and the checker/exporter/Landrun
  executable hashes. All ten exact dependency revisions appear in the actual
  dependency log and equal the committed manifest and local acceptance pins.
- The actual log builds every one of the 30 local NLA modules in the independently
  reconstructed final import closure, then the canonical Solution wrapper.
  Challenge has exactly its 24 intentional specification holes. Solution and
  its final imports have no admitted-proof diagnostic. Both exported theorem
  lists match the configured ordered 24 names. Every Solution axiom report
  contains exactly `propext`, `Classical.choice` and `Quot.sound`.
  Default-kernel replay accepts the solution, then Comparator reports acceptance.
  The observed unused-simp/tactic/variable and proof-style warnings do not hide a
  compiler failure or forbidden axiom.
- The unchanged explicit kernel-mode LeanCert half-positivity certificate is
  consumed by initial data validity and the iterative coefficient positivity
  argument. This runtime review does not add a new mathematical review claim.
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

I read the pinned Tau Ceti review guidance and its correctness, generality,
proof-quality, reuse and attribution rubrics, together with the pinned Comparator
README and harness trust model. Their source hashes remain exact. Kernel
acceptance does not certify informal mathematical fidelity; that remains the
scope of the separately sealed statement and source reviews. Existing review
manifests and payloads were checked without altering their stated scope.

The prior generic `ROOT-AUDIT.json` is retained and hash-bound as corroboration.
Its helper has a hardcoded `/root` reviewer label. I did not rerun that helper,
and do not attribute its invocation to this reviewer. The coordinator separately
reported executing that helper again as `/root` during this task, with unchanged
`ROOT-AUDIT.json` bytes; that root invocation is distinct from my audit.
The attached audit independently reconstructs its relevant checks and additionally
checks full raw-log/ZIP correspondence and source-review continuation.

No Lean, Lake, Comparator, cache or compiler was run by this reviewer. Git was
used only to read immutable objects and compare files. No proof/worktree, Git
state, workflow, publication, PR or count was changed. This report preserves
the separately recorded mathematical/code authorship and George Stepaniants's
Department of Computing and Mathematical Sciences, California Institute of
Technology credit, and publishes no personal contact address. A later
publication commit and upstream merge checkout require their applicable exact
source and runtime checks.
