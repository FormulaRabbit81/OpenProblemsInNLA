# Independent preservation and contribution review

**Date:** 17 September 2026. **Verdict: PASS for the bound files below.**
No mathematical, target-matching, preservation, or reproduction defect was
identified. The contribution establishes the exact value **d7 = 47** in the
retained complex, full coefficient-space closure model. It is ready for local
repository integration. This review does not authorize or record a push or a
pull request.

## Reviewer role and limits

This review was performed by the Codex agent `c3_equal_review`, the same
separate reviewer who wrote the frozen final research review and the independent
full-polynomial reverse-derivative checker. The reviewer did not construct the
original contact seed or author the forward-jet certificate. In the research
campaign, `mf14_lower` constructed and certified the contact, `mf14_upper`
contributed the upper-bound argument, and the coordinator assembled the proof.
For this contribution, `mf14_lower` prepared the relocated source and guarded
runner, `mf14_upper` prepared the standalone manuscript, and the coordinator
edited the canonical entry and resolution archive and ran repository checks.
The present review checks that packaging work; it is not an additional
independent mathematical referee beyond the original reviewer.

This review includes a fresh manuscript read, an independent rerun of both
exact implementations, and all eight rejection controls. The original
mathematical review remains at
[`source/reviews/exact-degree47-final-review.md`](../source/reviews/exact-degree47-final-review.md).
Neither review is external human peer review or proof-kernel verification.

## Frozen source and relocated execution

I compared every one of the ten files under `source/` with the corresponding
file in `NLA Workspace/mf14-exact-2026-09-17`, checking exact bytes, lengths and
SHA-256 digests. All ten agree with both the campaign and
[`input_manifest.json`](input_manifest.json). Internal `experiments/` and
`reviews/` paths, the exact rational seed, both original result files, and the
necessary arithmetic helpers are preserved. The independent checker imports
its own arithmetic helper and no author implementation. The retained helpers
contain unused older routines; those routines and their omitted older seeds
are not dependencies of these final checks.

The new runner uses explicit exceptions for its own checks, pins the input
manifest hash, rejects altered/missing/additional/symlinked source files,
rejects optimized Python, and probes its child flags. Children run with
`-E -B -s`, so their assertions remain enabled and Python environment options
are ignored. Both checkers run in a temporary copy. The author result must be
byte-identical; the independent result must match every field except its
elapsed runtime. The runner also explicitly checks exact contraction and
self-map formulas and inequalities, then revalidates the source. I found no
path or import change that removes a required proof dependency.

I independently ran the following from the contribution directory on Python
3.14.0, directing fresh results to a separate temporary directory:

```sh
python3 -B verification/verify.py --output-dir <temporary-directory>/reproduction
python3 -B verification/test_verifier.py
```

Both certificate reconstructions passed, with the author result byte-identical
and the independent result mathematically identical. The full coefficient and
reverse-derivative array digest was:

```
4012edce6b72a8816002444bfd56b97edf836e63a9797921ea81deb12643b2f3
```

All eight controls passed, including rejection of seed/manifest changes, an
extra source file, source symlinks, `-O`/`-OO`, and effective
`PYTHONOPTIMIZE`, and acceptance of safe `-E`. These are tests of the ordinary
reproduction and integrity boundary, not a claim of protection against a
malicious replacement of the runner or Python interpreter. The committed
preparer logs report the same outcomes; my rerun did not modify them or the
frozen source.

## Mathematical and manuscript correspondence

The standalone [TeX](../proof.tex) and [PDF](../proof.pdf) faithfully expand the
frozen [proof](../source/proof.md). I checked the actual third-product identity,
the remaining four gates, the 48 active coordinates, contraction and Jacobian
invertibility, all 129 coefficients in the scaling limit, and the matching
available-space dimension/irreducibility argument. The detailed original
mathematical audit remains linked above; no new mathematical dependency or
stronger scope was introduced by typesetting.

I compared the complete appendix active-index list directly with the seed:
its order agrees, and the sole fixed coordinate is index 48, `e8`. Exact
fraction comparisons also confirm every displayed bound: residual below
`10^-69`, inverse defect below `10^-57`, inverse norm below `4000`, author
Hessian below `2*10^12`, author contraction below `10^-29`, and independent
contraction below `6*10^-8`. The displayed independent Hessian integer agrees
with the independently reconstructed certificate.

The final **Theorem 1** is exactly `d7 = 47`, so the canonical theorem locator
is correct. This is complex closure in full `V128`, not exact representation
of every polynomial, real-field coverage, or stable numerical recovery.
The certificate alone does not establish membership, the full-space limit,
or the upper bound; all three arguments are present and reviewed. Neither a
smaller-budget auxiliary theorem nor an external dimension theorem is needed.

I visually inspected all six page images rendered from the final PDF; the
coordinator confirmed their origin from the bound PDF with no later edits.
No clipped text, missing symbols, overlap or broken equation/reference layout
was found. Compilation and the canonical PDF inspection were separately
performed by the preparer and coordinator; see [integration checks](../integration-checks.md).

## Original target and repository preservation

I read the worktree's `AGENTS.md` and `CONTRIBUTING.md`, the canonical MF-14
diff, and the `RESOLVED.md` diff. The original problem statement and all content
from its heading onward are byte-identical to the contribution base. The
original question remains the equality to 42 in the same complex `V128`
closure model; the stronger theorem supplies its negative answer and determines
the new maximum. Status remains `Solved`, with no ID, canonical path, or open
count change. Earlier degree-42 and degree-44 statements and attribution remain
visible, and the resolution archive explains their relation to the new theorem.

I confirmed that the old Webb degree-44 and Colbrook reference archives, the
ID registry and the catalog have no diff against the worktree base. The
coordinator's repository checks are documented in the integration record;
those repository tests were not rerun by this reviewer. The new package clearly
discloses AI assistance and the informal review level. No Lean, external human
review, public release, or exhaustive priority search is asserted.

## Source binding

The following hashes bind the files reviewed here. Paths are relative to this
contribution directory unless prefixed `repository:`. The input-manifest hash
transitively binds all ten preserved source files; I also directly compared
each of those files with the original campaign. Rebuilding a PDF may change its
bytes; a changed manuscript, runner or certificate needs an updated binding.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `proof.tex` | 20978 | `e40d718755ece3fab28651cce4a278aca973e1a1ca6ae0eb73bc8948c8fa0622` |
| `proof.pdf` | 90501 | `80712867ccf9cf5490ab8e672245d9c55773222f1578ae91d952c1da4e13f4b0` |
| `README.md` | 6664 | `d79bad8d1c7f419355fd8a0f64754836d1c957e0a373015a6a3ee238c72834eb` |
| `PR_DRAFT.md` | 1558 | `9d83a417ba06087b1f073e641d083300259be644fc1f27cb41ced51a87fa6965` |
| `verification/verify.py` | 11780 | `fab8641d82c2745b4f8ba44bac9409b06d7e0c97c7418a9a37db41be579c95be` |
| `verification/test_verifier.py` | 3809 | `816b387f8f1f43f16369aaf5190aec5f9ca12553433101f7d65e84accd170faf` |
| `verification/input_manifest.json` | 2782 | `953116f9dd40f8c584a2f9cf1af840533c37ff9ced08f741ae901658f917d68b` |
| `verification/README.md` | 5222 | `0e5174ea0524a8ce9d7295c06cc31415b1e49835e6f2948fd939df83cd11ab93` |
| `source/proof.md` | 8916 | `d9fb806135cfa84806f207568db6de2270981a9705f43962eeb152f53a14bffa` |
| `source/reviews/exact-degree47-final-review.md` | 12638 | `3c3d551758a2abf780b7e1bf1487d52bb75c14956a433b35617418a152997ebd` |
| `integration-checks.md` | 3734 | `933e706ec4355e8bda7aef51da492051db70855e1d06f627f57506b22e45989e` |
| `repository:matrix-functions-and-stability/MF-14/README.md` | 8934 | `e6c56268cac558fd2c816a9d68f39f5eb3703ef8ad2682502f7a98092466888b` |
| `repository:RESOLVED.md` | 219659 | `ce3f5e4daf3200272ff54cc9204fca5f409ca7c30b43fab1cb3e740b9bd63c3e` |
