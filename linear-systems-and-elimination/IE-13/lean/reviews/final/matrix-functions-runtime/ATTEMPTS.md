# Audit preparation transparency

The first execution of this independent Python audit stopped while attempting
to read `tools/lean/sandbox_probe.py`, a nonexistent repository path. That was
an audit-path mistake; no acceptance report was written. The committed harness
actually creates its CI probe by a checked text transformation of the pinned
Forsythe probe. The corrected audit authenticates the pinned original bytes,
extracts only the pure `ci_probe_source` text-transformation function from the
committed harness, and hashes its output against the actual runtime receipt.
This does not run Lean or execute a sandbox probe locally.

A second preparation execution stopped at a case-sensitive package lookup:
the manifest names the package `leancert`, whereas the first audit draft used
the Lean module capitalization `LeanCert`. The lookup was corrected to the
actual manifest key. This likewise wrote no acceptance report and changed no
input or runtime evidence.
