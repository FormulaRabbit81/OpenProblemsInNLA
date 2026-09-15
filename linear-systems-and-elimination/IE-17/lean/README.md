# IE-17: both LSMR backward errors can increase

**Verification stage: complete local proof candidate.** All eight exported
statements compile and pass local kernel-trust and permitted-axiom checks.
Independent final source review and fresh isolated Linux Comparator verification
remain pending. The canonical problem remains **Solved**.

**Formalization:** George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with substantial OpenAI Codex
assistance. **Original mathematical counterexample:** Matthew J. Colbrook,
Department of Applied Mathematics and Theoretical Physics, University of Cambridge.
The [canonical entry](../README.md) and
[complete original manuscript](../../../references/colbrook-recovered-2026-09-11/manuscripts/IE-17.tex)
retain their full statements and original proof attribution.

## Complete target

One exact full-column-rank real `4 × 3` example has both canonical errors strictly
increase between the same first and second nonzero LSMR iterates. The proof uses
the actual Euclidean operator norm, all real matrix perturbations with the right
hand side fixed, and an attained minimum. The approximation uses the literal
stacked matrix and all four Moore–Penrose equations, with a proved unique value.

The exact LSMR run starts at zero, minimizes the normal-residual norm over the
entire real Krylov space, satisfies the minimum-length convention, and first
terminates at step three. Both errors vanish at that exact terminal iterate.
The eight [Comparator exports](comparator.json) include separate negations of
both original monotonicity claims. The [numerical dossier](NUMERICAL_TARGETS.md)
records the independently reviewed exact fractions and every correspondence gate.

## Proof structure

| Module under `NLA/IE17/` | Role |
| --- | --- |
| `Definitions.lean` | Frozen actual norms, residuals, perturbations, Krylov spaces, finite runs and four-law pseudoinverse semantics |
| `Norms.lean` | Operator-norm semantics, closed feasibility, general minimum attainment by compactness |
| `Geometry.lean` | Euclidean inner products, adjoints and squared operator-norm bounds |
| `BackwardError.lean` | Covers both zero and nonzero perturbed residuals for every real perturbation |
| `NumericData.lean` | Exact coordinates and squared norms of the three iterates and residuals |
| `Certificates.lean` | Feasible rational perturbation, exact sum-of-squares upper/lower certificates, consumed LeanCert kernel cutoff |
| `Optimal.lean` | Attained optimal errors with the original strict separating bounds |
| `LSMR.lean` | Full real-span minimization, uniqueness/minimum length, exact Krylov membership and first termination |
| `Approximation.lean` | All four Penrose laws for the actual stack, projection uniqueness and both exact squared values |
| `Proof.lean` | Eight complete exports, both strict increases, both universal-claim counterexamples and kernel assertions |

The computation is exact. Sparse matrix structure replaces numerical inversion;
real-span orthogonality proves global minimization; rational sum-of-squares
identities prove bounds for all vectors. No sampling of perturbations or iterates
substitutes for the quantified claims. LeanCert certifies the rational cutoff
chain in explicit kernel mode, and the optimal-error proof consumes that chain.

`Challenge.lean` imports only frozen definitions and contains eight intentional
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
The retained local logs under `verification/` are development evidence.

Authoritative verification, from the repository root on the documented non-root
Linux host:

```bash
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py linear-systems-and-elimination/IE-17/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh linear-systems-and-elimination/IE-17/lean /absolute/path/to/nla-lean-tools
```

The shared [harness instructions](../../../tools/lean/HARNESS.md) specify the real
Landrun/Bubblewrap isolation, fresh committed-input snapshot, default-kernel
replay, axiom gates and rejection controls. No isolated Linux run is claimed yet.

## Independent review and metadata

Two non-implementing AI agents approved the exact boundary before proofs, frozen
at commit `5d9ae3c9`. The [freeze record](reviews/statement-freeze.json) and
both statement reports retain all ten input hashes. Those inputs remain unchanged.
Final review follows the repository [Tau Ceti adaptation](../../../docs/lean/REVIEW.md).
All reviews are AI-agent reviews; no external human peer review or official Tau
Ceti endorsement is asserted.

[formalization.yaml](formalization.yaml) records authorship, source attribution,
automation, all eight exports and the actual verification stage. Status promotion
requires both full-source approvals and reproducible Linux verification.
