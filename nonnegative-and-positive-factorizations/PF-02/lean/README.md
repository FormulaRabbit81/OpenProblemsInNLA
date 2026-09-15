# PF-02: minimal positive semidefinite factorization orbits can be disconnected

**Verification status: Lean verified.** All nine complete-target declarations
passed fresh isolated Linux Comparator, default-kernel replay and permitted-axiom
checks. Both independent complete-source reviews and both operational audits passed.

**Formalization:** George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with substantial OpenAI Codex
assistance. **Original mathematical counterexample:** Matthew J. Colbrook,
Department of Applied Mathematics and Theoretical Physics, University of Cambridge.
The [canonical entry](../README.md) and
[complete original manuscript](../../../references/colbrook-factorization-2026-09-11/manuscripts/PF-02_disconnected_orbits.tex)
retain their full statements and original proof attribution.

## Complete target

The original question asks whether the congruence orbit space of minimal real
positive semidefinite factorizations is connected whenever ordinary rank equals
`k(k+1)/2` and PSD rank equals `k`, for every `k ≥ 3` and every allowed matrix
size. One strictly positive integer `6 × 6` matrix refutes this universal claim.
It has actual ordinary rank six, an attained minimum PSD factor size of three,
and a disconnected quotient of its entire size-three factorization space.

The definitions include every pair of real PSD factor families satisfying all
trace equations, their Euclidean subspace topology, every real invertible
congruence and the actual quotient topology. Row and column families may be
unrelated, and arbitrary factors may be singular. The two explicit examples
have positive definite factors and opposite orientation determinants, `32` and
`-32`; the proof does not restrict the factorization space to those examples.

For every factorization of this matrix the coordinate determinant is nonzero.
Under every real invertible congruence it is multiplied by the positive fourth
power of the change-of-basis determinant. Its sign therefore descends to a
continuous surjection from the actual orbit quotient onto discrete `Bool`.
This proves disconnectedness, with no path or Hausdorff assumption.

The nine [Comparator exports](comparator.json) include the exact generic orbit
semantics and the negation of the full original universally quantified claim.
The [mathematical and numerical dossier](NUMERICAL_TARGETS.md) records the
independently reviewed correspondence and certificates.

**Scope:** the formalization establishes the complete negative answer using the
manuscript's explicit size-three counterexample (Theorem 1). It does not claim
the additional constructions for every factor size, the nonquantitative positive
rational perturbation argument, or a classification of connected components.
Those further results and their original attribution remain preserved in the
complete manuscript.

## Proof structure

| Module under `NLA/PF02/` | Role |
| --- | --- |
| `Definitions.lean` | Frozen actual PSD factor tuples, attained minimum PSD rank, ordinary rank, congruence relation and quotient topology |
| `Data.lean` | Both PD witnesses, all trace equations, exact determinants and rank, consumed LeanCert kernel positivity certificate |
| `Coordinates.lean` | Generic symmetric trace pairing and covariance for all real congruence matrices |
| `CongruencePolynomial.lean` | Full symbolic determinant identity and sign preservation under every real invertible congruence |
| `Action.lean` | The actual change of basis preserves PSD and trace equations in arbitrary dimensions; the relation equals a single transformed factorization |
| `Rank.lean` | Generic trace-factor rank bound, exclusion of every smaller positive factor size, actual attained minimum |
| `Orbits.lean` | Exact relation equivalence, single-congruence quotient equality and quotient-map semantics |
| `Topology.lean` | Nonvanishing on the whole factor space, continuous sign descent, surjectivity and disconnectedness |
| `Proof.lean` | Nine exact exports, universal-claim counterexample, kernel assertions and axiom reports |

All computation is exact. Quadratic inequalities establish positive definiteness
for every real vector. The kernel-certified `eval_det` tactic uses Bird's
algorithm and ring arithmetic for determinant calculations, including the
nine-variable identity `det C(S) = (det S)^4`. The simpler general bound
`rank M ≤ k²` suffices to exclude sizes one and two while preserving the actual
PSD-rank target. LeanCert certifies `0 < (32 : ℝ)` in explicit kernel mode, and
the quotient separator's surjectivity proof consumes it.

`Challenge.lean` imports only frozen definitions and contains nine intentional
specification placeholders. `Solution.lean` imports the complete proof separately.
No target definition is a replaceable Comparator hole. The permitted axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

## Reproduction

The complete dependency graph and toolchain are pinned. Local development:

```bash
lake exe cache get
lake build Solution
lake build Challenge
```

The pre-proof default build target remains `Challenge`; `lake build Solution` is
the explicit proof build. A successful Challenge build alone establishes no proof.
The retained [Solution build log](verification/local-solution-build.log) and
[Challenge build log](verification/local-challenge-build.log) are local development
evidence, not isolated Linux verification.

Authoritative verification, from the repository root on the documented non-root
Linux host:

```bash
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py nonnegative-and-positive-factorizations/PF-02/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh nonnegative-and-positive-factorizations/PF-02/lean /absolute/path/to/nla-lean-tools
```

The shared [harness instructions](../../../tools/lean/HARNESS.md) specify real
Landrun/Bubblewrap isolation, a fresh committed-input snapshot, default-kernel
replay, axiom gates and rejection controls. The successful authoritative run is
recorded below.

## Independent review and metadata

Two non-implementing AI agents approved the exact boundary before proofs, frozen
at commit `a128cc3a`. The [freeze record](reviews/statement-freeze.json) and
both statement reports retain all ten input hashes. Those inputs remain unchanged.
Both independent complete-source reviews approved: [referee 1](reviews/final-referee-1.md)
and [referee 2](reviews/final-referee-2.md), following the repository
[Tau Ceti adaptation](../../../docs/lean/REVIEW.md).
All reviews are AI-agent reviews; no external human peer review or official Tau
Ceti endorsement is asserted.

[formalization.yaml](formalization.yaml) records authorship, source attribution,
automation, all nine exports and the completed verification stage. Complete-target
correspondence, both full-source approvals and reproducible Linux verification
with permitted-axiom checks support this status.


## Authoritative Linux verification

[Run 35021020857, attempt 1](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35021020857/attempts/1) verified immutable proof revision
[`a3e984ce`](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/a3e984ced348f4d8529c5d0f8f87c9be7dd979e2/nonnegative-and-positive-factorizations/PF-02/lean)
on Ubuntu 24.04. The target verification job completed all nine Challenge/Solution
comparisons, transitive permitted-axiom checks, default-kernel replay, real sandbox
probes, three raw-kernel controls, five Comparator regressions, and separate
sorry/native rejection controls.

The [permanent archive](verification/linux-2026-09-15/) retains the original ZIP,
all extracted members, GitHub provenance and the full source receipt. Artifact
`10418540042` has SHA-256
`a62edf32bfdf4ef70abcabe572ca8fffb6ba2b0d2f4f6ddc879df99229ffb6c9`.

```bash
cd verification/linux-2026-09-15
shasum -a 256 -c SHA256SUMS
```

Both independent operational audits approved: [referee 1](reviews/linux-referee-1.md)
and [referee 2](reviews/linux-referee-2.md). Each checked all
70 candidate input hashes against the verified Git revision
and previously approved source. The standalone checker-controls workflow job was
skipped because shared tools were unchanged; all required controls ran within
the actual PF-02 verify job.

Publication changes update status, documentation, evidence and rendered artifacts.
The mathematical statements, proofs and dependency inputs remain those verified
at the immutable proof revision. Pending-stage wording inside historical reports
is closed by these later approvals. No second independent Linux execution or
external human review is claimed.
