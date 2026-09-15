# IE-15: exact small-order rook-pivoting growth

**Current verification stage:** complete local Lean build and two independent final
source approvals; fresh Linux Comparator verification is pending. The canonical
entry remains **Solved** until all required checks pass.

**Original mathematical proof and formalization credit:** George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology. The formalization was developed with substantial OpenAI Codex
assistance. Historical problem attribution and the original proof remain in the
[canonical entry](../README.md) and [original solution](../solution.md).

## Complete target

For every real nonsingular input in order three or four, and every admissible
rook-pivoting path including ties, the maximum entry magnitude over **all** active
matrices is bounded by the original maximum entry magnitude times `3` or `14/3`.
The exact rational witnesses attain these constants. Consequently

```text
g_RP(3) = 3,    g_RP(4) = 14/3.
```

The eight checked declarations are selected by [comparator.json](comparator.json).
They include both all-entry upper bounds, both attained witnesses, greatest-element
statements for both growth sets, their actual real supremum equalities, and the
meaning of the initial finite maximum. The [numerical dossier](NUMERICAL_TARGETS.md)
records every domain, constant and correspondence obligation.

## Proof structure

| Module under `NLA/IE15/` | Role |
| --- | --- |
| `Definitions.lean` | Frozen real matrices, literal row/column swaps, Schur updates, all-path semantics and finite maxima |
| `Basic.lean` | Maximum semantics, factor-two step bound, and growth from all-entry bounds |
| `Permutation.lean` | Exactly preserves every stage maximum while moving arbitrary pivot choices to diagonal order |
| `Normalization.lean` | Preserves all stage magnitudes under positive scaling and row/column sign changes |
| `Coordinates.lean` | Reconstructs original entries from actual Schur residuals and preceding updates |
| `Scalar.lean` | Full signed two-pivot inequality and exact bilinear bounds |
| `FourthScalar.lean` | Complete order-four coordinate inequality |
| `NormalizedBounds.lean` | Applies scalar inequalities to the actual normalized matrices |
| `Reduction.lean` | Transports the normalized final-pivot bounds to every entry of every original rook path |
| `Witnesses.lean` | Exact determinants, admissibility, trajectories and growth of both rational witnesses |
| `Proof.lean` | All eight complete exports and their transitive kernel-trust assertions |

`Challenge.lean` imports only the frozen definitions and has eight intentional
specification placeholders. `Solution.lean` imports the complete proof in a
separate environment. The final axiom allowlist is exactly `propext`,
`Classical.choice`, and `Quot.sound`; target definitions are not replaceable holes.

The proof uses exact algebra throughout. The only LeanCert calculation certifies
`4 ≤ 14/3` in explicit kernel mode, and that fact is consumed when including the
third active stage in the order-four upper bound. The scalar argument replaces
the source's piecewise auxiliary monotonicity calculation with a proved polynomial
inequality. Direct bilinear interpolation proves the four-corner estimate on the
entire unit square. All signed multiplier domains are retained.

## Reproduction

The toolchain and complete dependency graph are pinned by `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json`.

For a local development check, with the pinned toolchain selected:

```bash
lake exe cache get
lake build
lake build Challenge
```

The local log [verification/local-solution-build.log](verification/local-solution-build.log)
records all eight export axiom reports and the auxiliary LeanCert certificate.
Development builds are separate from authoritative isolated verification.

From the repository root on the documented non-root Linux host:

```bash
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py linear-systems-and-elimination/IE-15/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh linear-systems-and-elimination/IE-15/lean /absolute/path/to/nla-lean-tools
```

The shared [harness instructions](../../../tools/lean/HARNESS.md) specify the real
Landrun/Bubblewrap sandbox, user service prerequisites, raw-kernel replay, and
negative controls. The verifier uses a fresh copy of committed inputs before any
solution build in that copy. An authoritative successful IE-15 run has not yet been
recorded at this development stage.

## Review and metadata

Two independent AI agents approved the exact pre-proof boundary at commit
`339a1da0`; the [freeze record](reviews/statement-freeze.json) and both statement
reports retain complete hashes. Both independent final referees approved the complete
source and original-target correspondence: [referee 1](reviews/final-referee-1.md)
and [referee 2](reviews/final-referee-2.md). Their reports record exact source hashes,
independent local rebuilds and permitted-axiom checks. All reviews are AI-agent reviews;
no external human peer review or official Tau Ceti endorsement is asserted.

[formalization.yaml](formalization.yaml) records authorship, attribution,
automation and the actual verification stage. All original problem statements,
permanent IDs and previously published verifications are retained.
