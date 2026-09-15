# PF-02: minimal positive semidefinite factorization orbits can be disconnected

**Verification stage: complete local proof candidate.** All nine exported
statements compile and pass local kernel-trust and permitted-axiom checks.
Independent final source review and fresh isolated Linux Comparator verification
remain pending. The canonical problem remains **Solved**.

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
replay, axiom gates and rejection controls. No isolated Linux run is claimed yet.

## Independent review and metadata

Two non-implementing AI agents approved the exact boundary before proofs, frozen
at commit `a128cc3a`. The [freeze record](reviews/statement-freeze.json) and
both statement reports retain all ten input hashes. Those inputs remain unchanged.
Final review follows the repository [Tau Ceti adaptation](../../../docs/lean/REVIEW.md).
All reviews are AI-agent reviews; no external human peer review or official Tau
Ceti endorsement is asserted.

[formalization.yaml](formalization.yaml) records authorship, source attribution,
automation, all nine exports and the actual verification stage. Status promotion
requires complete-target correspondence, both full-source approvals and
reproducible Linux verification with permitted-axiom checks.
