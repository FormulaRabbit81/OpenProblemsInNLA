# SP-05: a PSD minimizer for the positive definite Jordan–Kronecker product

**Stage: complete proof candidate; final verification pending.** The full local
`Solution` build passes for all six exports, with explicit kernel-trust assertions
and only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom
closures. Both independent exact-byte statement reviews approved before proof
implementation, at boundary commit `04d1de395494800390405f3df1645316fe7943c2`.
Final independent source reviews, isolated Linux Comparator/default-kernel checks,
and operational reviews are pending. The canonical problem remains **Solved**.

**Formalization:** George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with substantial OpenAI Codex
assistance. **Original mathematical proof:** Matthew J. Colbrook, Department of
Applied Mathematics and Theoretical Physics, University of Cambridge.
The complete [canonical statement](../README.md) and [original proof](../solution.md)
remain unchanged. The original conjecture remains credited to N. Kalantarova
and L. Tunçel. No external human review or author endorsement is claimed.

## Complete mathematical scope

For every n≥2 and every pair of real symmetric positive definite matrices A,B,
the minimum Rayleigh quotient of the actual `A ⊗ B` on the `+1` eigenspace of
the commutation matrix is at most its minimum on the `-1` eigenspace. Both
minima are proved to be attained using `IsLeast` on the sets of quotient values
of **all nonzero real vectors** in the respective sectors.

The stronger source theorem is also implemented: in every n≥1, a nonzero real
positive-semidefinite matrix X gives an eigenvector `vec X` at the global
minimum of `A ⊗ B + B ⊗ A`. Its positive eigenvalue is a lower Rayleigh bound
for every nonzero real vector. No commutativity, simple-spectrum, even-dimension,
or invertible-minimizer assumption is imposed. Singular PSD minimizers and
repeated eigenvalues are included. Singular PSD or indefinite input A,B are
outside the original target.

Definitions use literal mathematical objects: `Matrix.vec` stacks columns with
`(column,row)` indices; `commutationMatrix` is the actual permutation matrix;
`Matrix.kronecker` supplies the coefficient matrix; and the real quotient is
`dotProduct v (K *ᵥ v) / dotProduct v v`. Frobenius squared norms are actual sums
of entry squares and are connected to vector dot products by a proved identity.
No default matrix or Pi norm determines the target.

The [reviewed dossier](NUMERICAL_TARGETS.md) records the complete statement,
source hashes and mathematical obligations. The frozen
[Comparator configuration](comparator.json) lists all six results and allows
no replaceable definition holes. [formalization.yaml](formalization.yaml)
records the current proof scope and pending verification gates.

## Proof structure and computation

| Modules | Mathematical content |
| --- | --- |
| `Certificates`, `Basic` | Literal vectorization, Kronecker and commutation identities. The skew matrix `E₀₁−E₁₀` has squared Frobenius norm 2 in every n≥2. The explicit LeanCert kernel certificate `0 < 2` proves it is nonzero and supplies a vector that can be normalized for skew-sector attainment. |
| `Complexification` | The actual entrywise real-to-complex star-algebra map preserves PSD/PD, inverses of units, PSD square roots and absolute values. Square-root uniqueness proves the modulus of `iW` is the complexification of a real PSD matrix, including singular W. |
| `Sylvester`, `Cone` | Full complex Jordan-equation uniqueness and Hermitian solution symmetry. Congruence reduces inverse positivity to `CX+XC≥0` with C positive definite. A negative eigenvalue of Hermitian X would give a negative quadratic form, so X is PSD. Exact inverse coefficient and vectorization identities instantiate this result for the actual Jordan inverse. |
| `Modulus` | The Hermitian positive/negative parts yield two individually nonnegative cross terms. Their sum proves the modulus quadratic comparison without an additional self-adjointness premise in this helper. Exact trace identities prove preservation of the Frobenius squared norm. |
| `Spectral`, `Jordan`, `Minimizer` | A maximum from the finite real eigenvalue set gives a PSD slack matrix. A zero PSD quadratic form gives its kernel equation. Reciprocal positive eigenvalue bounds give the all-vector global minimum for the original Jordan matrix, with a real nonzero PSD eigenmatrix. |
| `Sectors`, `Proof` | The dot-product unit sectors are closed subsets of the coordinate box `[-1,1]`, hence compact. Explicit normalization proves that attained unit-sector minima equal the original full-sector minima. The exact factor-two identity yields the canonical inequality. |

The inverse-cone proof establishes the same property used by the original
manuscript without implementing its exponential integral. The modulus argument
uses `2 tr(P Φ(N)) + 2 tr(N Φ(P)) ≥ 0`; the source combines these terms into
`4 tr(P Φ(N))` using self-adjointness. The formal proof proves each sign directly.
These are exact proof simplifications and introduce no new target hypotheses.

There is no sampled spectral calculation, expanded characteristic polynomial,
or approximate extremal eigenvalue. The only LeanCert interval calculation is
the consumed rational positivity certificate. All matrix dimensions, entries,
cone arguments and spectral comparisons remain symbolic.

## Exported results

All names below are in namespace `NLA.SP05` and are checked against the six
independently reviewed Challenge declarations:

| Declaration | Exact role |
| --- | --- |
| `numerical_bound` | Consumed kernel certificate `(0 : ℝ) < 2`. |
| `column_vectorization` | Actual Kronecker action, transpose permutation and Euclidean/Frobenius identity for arbitrary real matrices. |
| `skew_witness` | Skew symmetry, squared norm 2 and nonzero witness for every n≥2. |
| `positive_minimizer` | Real nonzero PSD eigenmatrix at a positive global Jordan minimum for every n≥1. |
| `sector_minima` | Attainment and universal minimality in both complete sectors for every n≥2. |
| `canonical_result` | Both attained minima and their comparison for every original admissible A,B,n. |

## Reproduction and evidence

Run the Python commands in an environment with the dependencies from
[tools/lean/requirements.txt](../../../tools/lean/requirements.txt).

```bash
lake exe cache get
lake build Challenge
lake build Solution
python3 ../../../tools/lean/validate_manifest.py .
python3 reviews/initial/independent-exact-check.py
```

Pins: Lean **4.33.1**, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`.
The default Lake target remains the frozen Challenge. Its six intentional
specification placeholders establish no theorem and are excluded from the
zero proof-development sorry counts. `Solution` imports the implemented proofs
and does not import Challenge.

The complete local build log is
[verification/local-solution-build.log](verification/local-solution-build.log).
It records success for all six target closures and their permitted axioms.
Two harmless unused-hypothesis warnings occur because the sector-attainment
lemma is proved for arbitrary A,B; the reviewed wrapper retains its exact
positive-definiteness hypotheses. The
[contributor-support archive](verification/contributor-support/README.md)
retains successful support-module compiler traces and source/freeze hashes.
It is local contributor evidence, not an independent final review or an
isolated Linux verification.

The optional exact Python diagnostics check conventions on a noncommuting 2×2
example and verify preserved source hashes. They are not a finite-example proof
of this universal result.

## Independent review and remaining gates

The [statement freeze](reviews/statement-freeze.json) retains all ten approved
input hashes and both sealed statement reports:
[referee 1](reviews/statement-referee-1.md) and
[referee 2](reviews/statement-referee-2.md).
Those inputs remain unchanged after implementation. The two referees contributed
no proof code. Their statement approvals are distinct from the pending final
source and operational reviews.

The repository [review protocol](../../../docs/lean/REVIEW.md) applies Tau Ceti
referee standards through independent AI-agent reviews. Actual pinned Lean4
Comparator, default-kernel replay, real sandbox probes and rejection controls
must still run through the [Linux harness](../../../tools/lean/HARNESS.md) for
this candidate. A local macOS build does not complete those gates. Status
promotion and publication must wait for complete-target correspondence,
reproducible isolated verification and all required approvals.

The pinned [Forsythe](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof)
and [Schiffer](https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1)
projects supply structure/API references. No mathematical implementation was
copied from them. No official Tau Ceti endorsement, external human review,
novelty certification or unmeasured cost claim is made.
