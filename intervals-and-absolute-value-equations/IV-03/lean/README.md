# IV-03 Lean formalization

This project proves the complete IV-03 equivalence in every positive dimension:
for any ordered real entrywise endpoints, the entire closed matrix interval
consists of inverse M-matrices exactly when the prescribed vertices do. It
proves both the stronger n-squared negative-sign criterion and the original
two-sign criterion, together with the exact vertex formula and admissibility.
Zero widths, zero entries, reducible matrices, and arbitrary nonsymmetric
endpoints are retained. There is no interval regularity or nonsingularity premise.

**Mathematical argument: Matthew J. Colbrook**, Department of Applied Mathematics
and Theoretical Physics, University of Cambridge. **Existing formalization:
Sidney Holden**, with OpenAI Codex assistance, under [Apache-2.0](LICENSE).
**Integration and verification submission: George Stepaniants**, Department of
Computing and Mathematical Sciences, California Institute of Technology.
The existing mathematical and formalization authorship is preserved.

The implementation is imported unchanged from [Sidney Holden's immutable
revision](https://github.com/sidneyholden1/OpenProblemsInNLA/tree/281f440650d174602120ca9b2b930d38f9fef205/intervals-and-absolute-value-equations/IV-03/lean).
All 75 original project inputs were retrieved through the GitHub Git tree/blob
API and hash-checked. Only this README and the formalization metadata are updated
for integration; their original bytes are retained in the [import record](verification/campaign-import-2026-09-16/TRANSITION.json).
All 14 active Lean files, seven frozen inputs, dependency pins, license, original
review records, numerical plan, and statement freeze remain unchanged.

**The fresh campaign verification run is pending.** The authenticated historical
[Linux run 34926260380](https://github.com/sidneyholden1/OpenProblemsInNLA/actions/runs/34926260380)
accepted all four exports using LeanCert kernel-trust checks, Comparator and
Lean's default-kernel replay at `516ad4a0e85c21c7ef34507db9ab3b68b393bb90`.
Actual sandbox, kernel replay, statement-mismatch, and illegal-axiom rejection
controls also passed. All mathematical bytes at that tested revision equal the
imported revision. Two additional independent nonimplementing AI agents have
reviewed the entire proof and original target and independently reconciled the
historical execution. Their [reports](reviews/campaign/README.md) and the
[historical evidence](verification/historical-linux-34926260380/README.md) are
retained. These historical checks do not assert that the new integration commit
has already run, and this package does not change a canonical status or count.

Start with the [numerical targets](NUMERICAL_TARGETS.md), [definitions](NLA/IV03/Definitions.lean),
[Challenge](Challenge.lean), [proof notes](PROOF_NOTES.md), and four
[Solution exports](Solution.lean). `IsInverseM` includes genuine invertibility,
entrywise nonnegativity, and the required signs of the actual inverse. The
[statement freeze](statement-freeze.json) records the original reviewed boundary.
Challenge's four deliberate specification placeholders are never imported by
the thirteen-file Solution closure. Earlier pending-stage prose in the retained
numerical plan and source provenance is historical.

Exact weighted maximum principles, block inverse identities, complementary
minors, and adjugate completion establish the full result. A resolvent identity
and three genuine interval members replace derivative comparisons. This avoids
numerical interval grids and approximation. Solution contains four LeanCert
`#assert_trust kernel` checks; only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. Complexity estimates are outside the formalized equivalence.

With the pinned dependencies available, run `lake build` or `lake build Solution`
from this directory. The original default target already selects Solution.
Authoritative verification uses the shared [nonroot Linux harness](../../../tools/lean/HARNESS.md)
from the repository root:

```sh
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh intervals-and-absolute-value-equations/IV-03/lean /absolute/path/to/nla-lean-tools
```

The [metadata](formalization.yaml) follows schema v0.4. Reviews apply the
repository's scoped Tau Ceti protocol; no official endorsement or human peer
review is claimed. The Schiffer and Forsythe examples inform the shared proof
organization and checking protocol. No local Lean or Lake run is claimed by
the integration campaign.
