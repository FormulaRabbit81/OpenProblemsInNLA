# Public duplicate-formalization audit and reused source

The 16 September 2026 04:04 UTC campaign audit covered 14 public repositories,
249 public branch heads and 203 unique nontruncated commit trees, plus 149
upstream PR records. Its KE-05 formalization hit was Sidney Holden's existing
commit `04f3f39beb69d77dbc4a8eadee70259eb89a591a`. This submission deliberately
integrates that Apache-2.0 implementation with its original formalization credit;
it does not claim a new independently authored Lean proof. All 23 mathematical
files are unchanged from Holden's source and its historically tested revision.

Upstream PR 143 already merged George Stepaniants's informal mathematical
solution. This PR adds reviewed Lean verification of that retained target.
The summary, full head list, relevant PRs and scan findings are retained here.
The original manifest records the larger raw archive's hashes without copying
all tree responses into the build. The audit excludes private, deleted, unpushed,
unusually named or otherwise undiscoverable work and makes no priority claim.
