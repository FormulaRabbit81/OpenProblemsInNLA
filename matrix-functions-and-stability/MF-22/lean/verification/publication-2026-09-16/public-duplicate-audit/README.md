# Public duplicate-formalization audit

The root campaign audit at 2026-09-16 04:04 UTC enumerated 14 public repositories,
249 API-listed public branch heads and 203 unique commit trees, plus 149 upstream
pull-request records. All complete nontruncated trees were scanned for the named
targets' Lean source and formalization manifests. This directory retains the
bounded findings, full head list, relevant PRs and hashes/references for the raw
archive; large raw Git-tree responses are not copied into the active proof build.

For MF-22 the only detected Lean hits were this campaign's development commit
`93abf01922d103993f2a92e819f207d63effbfae` and accepted standalone proof commit
`c701bfeea660473fc31ad9d0c74b76309be3b49f`. Upstream PR 120 was the already merged
informal solution, not a competing Lean formalization. Thus this audit found no
other public MF-22 formalization among its checked names and trees.

This is a bounded duplicate-formalization check, not a new literature search or
an assertion about private, deleted, unpushed or unusually named work. The original
problem is already mathematically solved; the new submission adds its Lean proof.
