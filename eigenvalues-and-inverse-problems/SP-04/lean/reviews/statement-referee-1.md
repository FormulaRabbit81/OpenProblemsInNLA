# SP-04 independent statement referee 1

**Verdict: APPROVE the exact pre-proof boundary.** The eleven signatures and
their imported definitions faithfully express the complete canonical negative
target. The numerical data and proposed mathematical proof route are sound.
No proof implementation or final kernel/Comparator verification is approved
by this report.

- **Reviewer:** OpenAI GPT-6 Codex agent `/root/reference_api_review`, an
  independent non-implementing AI referee.
- **Date/phase:** 15 September 2026; exact mathematical and numerical review
  before proof implementation.
- **Published base:** `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`.
- **Protocol:** repository [Tau Ceti adaptation](../../../../docs/lean/REVIEW.md),
  covering fidelity, correctness, scope, proof quality, reuse, generality,
  API design, naming, placement, documentation and attribution. This is not
  official Tau Ceti review or external human peer review.

I read the complete canonical README, original `solution.md`, preserved source
and historical proof review; all definitions and eleven Challenge signatures;
the aligned dossier, configuration, and retained initial diagnostic records.
I wrote and ran my own exact arithmetic checker before reading the author's
checker. I contributed no proof implementation or boundary edits.

## Exact approved inputs

All ten hashes were independently checked against both the actual project
and a fresh source snapshot. These are the approved bytes:

| Project-relative input | SHA256 |
| --- | --- |
| `NLA/SP04/Definitions.lean` | `6ec0afd466bfb054b9a46353f37a01e39333259e2579f21ae5fd52b5e9d57161` |
| `Challenge.lean` | `79aa3fe4ce1d75157f153b259660a8abd08cd8f0cecc7d0fad3ebcca0cf98381` |
| `NUMERICAL_TARGETS.md` | `e14351bfa611bf6f1d1c7302b0584866bb54074c9db3c1e8f43c1f5dee571290` |
| `comparator.json` | `d0783ec075a831cee2a501a46e02e42258b995f9fbf377dab1c749bba95457ff` |
| `lakefile.toml` | `1f4038f5e6c2f3ed9409d51f444f1ca2256b03a828d69b0dca855f61f2b082fd` |
| `lake-manifest.json` | `0b777416633b6ab6cecb4b739da1148251ec285a20225da94da6f72b56bddcab` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `reviews/initial/independent-exact-check.py` | `41729e1a69cb0b5e3aa314f6dfb4a427e16467edec5022de0ff29229b06123dc` |
| `reviews/initial/independent-exact-check.json` | `8333c86c264642f175a0134ccc085dbfd6b8051ee0ab1fdb08836e1d15e33873` |
| `reviews/initial/source-hashes.json` | `a5aa8f0e6f552ebd9045a18b623792a1af8155e5ba312685028776370dc210ea` |

The [execution record](statement-referee-1-evidence/execution-record.json)
also seals the complete canonical README, both original source formats and
the historical review. All four match the published base exactly. I separately
recovered the historical normalized theorem/proof block: **4714 UTF-8 bytes**,
SHA256 `77b6c6240eab1eab1cd7f9326a95a4bb7455188f951c11718c1b8c07cf691d95`.
That block hash is distinct from the whole-file source hashes. Permanent ID,
path, full original statement and original attribution remain preserved.

## Semantic fidelity and complete scope

`Feasible X` is the literal `|det X| = 1`; both determinant signs remain
available. `Stationary U X c` imposes the full real matrix equation
`Xᵀ(U-X)=cI` and feasibility. `stationaryPairs` is the entire matrix/multiplier
set, without a diagonal, sign, bounded-multiplier or selected-branch restriction.

`UniqueLeastStationary` asserts existence at the displayed pair and compares
its absolute multiplier with every real stationary pair. Equality forces
equality of both matrix and multiplier. Thus it addresses ties of opposite
multiplier signs and multiple matrices with the same multiplier. It is not
merely uniqueness within a chosen scalar branch.

`frobeniusNorm` is explicitly `Real.sqrt (Σ i, Σ j, X i j ^ 2)`. It does not
use the default matrix norm, which would be unsuitable for this objective.
`IsNearest` states feasibility plus the actual global inequality against every
feasible matrix. Consequently a strictly improving feasible matrix refutes
nearestness directly; no unproved infimum/attainment convention is involved.

`RegularData` means invertibility and nonduplication of the real Gram
characteristic roots. Root-list nonduplication would be insufficient for an
arbitrary nonsplitting real polynomial. Here the Gram matrix is real Hermitian:
the pinned `Matrix.IsHermitian.splits_charpoly` and
`roots_charpoly_eq_eigenvalues` establish that its roots exhaust the spectrum.
The definition therefore expresses actual distinct squared singular values.
The `regular_svd` export explicitly obliges the proofs to establish this for
the witness data.

The genericity quantifiers are correct. `GenericSelectionRule n` permits an
arbitrary nonzero polynomial in all n² entries as an exceptional zero set.
`generic_counterexamples` quantifies over **every** nonzero polynomial in all
nine entries, producing outside its zero set a regular datum with a finite
full stationary set, an actual unique least pair and a strictly better feasible
matrix. Each premise of the claimed rule must be proved for that datum.
An arbitrary proper real algebraic set is contained in the zero set of some
nonzero defining polynomial, so this defeats every permitted algebraic
exception. The final `¬ AllGenericSelectionRules` retains all dimensions n≥2
and refutes the n=3 instance. No finiteness or uniqueness premise makes the
counterexample vacuous.

## Eleven exact obligations

| Export under `NLA.SP04` | Reviewed obligation |
| --- | --- |
| `numerical_bounds` | Four literal strict rational inequalities with the intended real casts. |
| `diagonal_stationary_iff` | Both directions for every real X and c at every admissible triple; all quadratic root choices and both product signs. |
| `diagonal_counterexample` | Every strictly ordered triple in the entire original box; actual square-root selected entries; unique least pair; feasible sign-flipped improvement in the unsquared Frobenius norm. |
| `diagonal_finite` | Finiteness of the entire real stationary-pair set, including all multipliers. |
| `orthogonal_transport` | All dimensions and all real P,Q satisfying both orthogonality equations; feasibility equivalence, exact norm preservation and stationarity equivalence with unchanged c. |
| `spectral_family` | A nonempty full-ambient open set and a genuine two-sided orthogonal SVD with singular entries in the original box. |
| `regular_svd` | Actual invertibility and simple real Gram spectrum for every such SVD. |
| `open_family_counterexamples` | Every family member has all components of `SelectionFails`, including full finiteness and unique global multiplier selection. |
| `algebraic_avoidance` | Every nonempty open subset of all real 3-by-3 matrices escapes each nonzero nine-variable polynomial zero set. |
| `generic_counterexamples` | Complete regular failures outside every proposed polynomial exception. |
| `canonical_counterexample` | Negation of the original all-dimension algebraic-generic rule. |

Comparator lists precisely these eleven names and has no replaceable definition
holes. `Solution.lean` currently imports only definitions. The eleven Challenge
placeholders are deliberate specifications and establish no theorem.

## Independent mathematical audit

**All stationary matrices.** Feasibility makes X invertible. With S=XᵀX,
the stationary equation gives `UᵀU=S+2cI+c²S⁻¹`, so S commutes with the
diagonal Gram matrix. Distinct positive sᵢ make its squared entries distinct,
forcing S diagonal. The equation `XᵀD=S+cI`, with each sᵢ nonzero, then forces
X diagonal directly. The dossier's simplification avoids an unnecessary
inverse while retaining every real stationary matrix and both signs.

**Selection and strict improvement.** The discriminant lower bound is
`393/400 > (99/100)^2`. The rationalized square-root difference yields
the coefficient `25/18 = 275/198 < 2`, and the width 1/100 gives a large-root
range below 1/72 < 1/50. The competing positive-branch product is bounded by
`14586/15625 < 1`. The all-large product exceeds one. This covers all eight
patterns for `0<c≤13/25`; c=0 is excluded separately. Positive multipliers
above the cutoff cannot compete with the constructed smaller absolute value.

For negative c=−t, the positive and negative-magnitude roots are strictly
increasing with t. Their product `g=b₁a₂a₃` starts at zero and exceeds one
at 13/25 by the exact tests `4−2(7/4)−13/25=−1/50` and
`1/16+(44/25)/4=201/400<13/25`. Continuity gives a unique t*. At fixed t>0,
`0<q₃<q₂<q₁<1`, where qᵢ=t/aᵢ². Among all nonempty negative-index subsets,
the unique largest product is the singleton {1}. Therefore no other pattern
is feasible before t*, and at t* only the displayed pattern is feasible.
No asymptotic enumeration of later crossings is required for this conclusion.
Changing the first sign preserves absolute determinant and improves squared
distance by `4s₁b₁>0`; nonnegative square-root monotonicity yields the required
strict unsquared inequality.

**Full open family and SVD.** The family contains exactly three strict
product-negative Gram-determinant conditions, one at each pair of endpoints.
It contains no SVD, regularity, finiteness or failure assertion as a premise.
Each condition is a polynomial strict inequality in all nine entries. The
standard matrix topology is the finite real product topology, so this is a
full nine-dimensional open set. My independent calculation confirmed all six
endpoint numerators over 10¹⁸:

```text
-1937653044525, 905786883351, 648098176275,
-649206984825, -910443880269, 1954285183575.
```

The three positive disjoint intervals yield three distinct Gram-characteristic
roots. Since that polynomial is monic of degree three, these exhaust its roots,
with multiplicity one. Its real Hermitian spectral decomposition and finite
reordering give Q; `P=U Q diag(1/sᵢ)` yields the actual orthogonal SVD. Both
orthogonal determinant signs are allowed. Inverting the transport bijects the
full stationary sets, not merely their displayed diagonal representatives.
The endpoints at 7/4 and 44/25 are harmless because the root intervals are open.

**Finiteness of every multiplier branch.** The proposed Kronecker eliminant
route is valid without an unformalized elimination specification. Each
companion Tᵢ maps `(xᵢ,1)` to xᵢ times itself using the actual scalar quadratic.
The tensor vector has last coordinate one, so it is nonzero. Its eigenvalue
under K is the signed product ±1. Consequently `det(K−I)det(K+I)` vanishes
at every stationary multiplier. At c=0, K is lower triangular with diagonal
`(s₁s₂s₃,0,…,0)`, giving exactly `R(0)=1−(s₁s₂s₃)^2≠0`. Thus R is a
nonzero polynomial with finitely many real roots. Each fixed multiplier allows
only finitely many triples of roots of three monic quadratics. Combined with
the full stationary reduction, this proves full-set finiteness, including all
positive multipliers and collisions outside the selected range. No expansion
of the eliminant coefficients is needed.

**Algebraic avoidance.** A nonempty ambient open set contains a product of nine
open intervals, each infinite. The actual pinned `MvPolynomial.funext_set`
then prevents a nonzero polynomial from vanishing on the whole box. This proves
the stated general avoidance lemma without treating a diagonal subspace as
ambient-open or assuming the desired genericity as an axiom.

## Independent execution and evidence

I made a fresh source snapshot with no project build artifacts, reusing pinned
dependency caches after checking all ten revisions and tracked-file cleanliness.
With Lean 4.33.1, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Darwin arm64:

- `lake build Challenge` exited 0: **2386 jobs**, exactly **eleven** intended
  specification-hole warnings.
- `lake env lean AuditBoundary.lean` exited 0. The audit printed 15 actual
  semantic definitions, all eleven types, the real matrix topology instances
  and the actual polynomial-variable cardinality **9**. It also typechecked
  the relevant spectral, polynomial, Kronecker and norm API names.
- My independent standard-library rational checker passed **49 checks**.
  In addition to the six Gram signs and all scalar constants, it uses a
  different exact stationary sample, t=2487/5000, to check the literal matrix
  equation, both determinant signs, strict squared-distance improvement,
  the nonzero tensor eigenvector, actual eliminant vanishing and nonzero
  evaluation at zero. A rational nondiagonal two-sided orthogonal transport
  checks both orientations and exact norm/multiplier preservation. These
  computations are diagnostics, not proofs of universal selection or genericity.

The [evidence directory](statement-referee-1-evidence/README.md) retains the
fresh logs, API audit, independent arithmetic program/output, exact hash checks
and [SHA256SUMS](statement-referee-1-evidence/SHA256SUMS). The execution-record
SHA256 is `c469243197486330ac7e5c6750e38296b113f67152e2bb4d1fbc4b80f0bf484b`.
The independent arithmetic-output SHA256 is
`a3287d30bdab8e8ff9cce1028c6912fe23a827b4caa78bd52fc7b05c3b9d3478`.

## Reuse, proof quality and remaining obligations

The definitions are direct mathematical predicates with descriptive names and
appropriate dimensional generality. The literal Frobenius definition avoids
norm-instance ambiguity; Mathlib's Frobenius API remains available for a proved
bridge if useful. I inspected the actual pinned spectral factorization/root
APIs, multivariate infinite-box uniqueness, matrix topology and univariate
root-finiteness APIs. These support the planned proof and avoid reimplementing
a general SVD, spectral continuity or full elimination algorithm.

The computation plan is proportionate: exact scalar estimates, eight finite
root patterns, three Gram intervals and the eliminant's nonzero evaluation.
The proposed LeanCert certificate is the closed strict rational product bound
and must actually be consumed in the subsequent positive-branch exclusion.
All quantified square-root, spectral, finite-set and genericity assertions
still require kernel proofs; the diagnostics and present typecheck do not
establish them.

New formalization attribution gives George Stepaniants and the complete
Department of Computing and Mathematical Sciences, California Institute of
Technology affiliation, with substantial Codex assistance and no new contact
email. The complete historical source and Matthew J. Colbrook's original proof
attribution remain unchanged. The dossier preserves the original question's
attribution to Baaijens and Draisma and distinguishes the stationary-pair target
from an independently implemented elimination algorithm.

**No blocking boundary finding.** Approval is specific to these ten hashes.
Proof implementation may follow after both independent pre-proof approvals.
Final full-source review, permitted-axiom checks, actual consumed LeanCert
kernel certification and reproducible Linux/Comparator verification remain
required before any **Lean verified** promotion. Canonical status remains
**Solved** at this review.
