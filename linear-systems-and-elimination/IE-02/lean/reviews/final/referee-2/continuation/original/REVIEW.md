# IE-02 independent full referee #2 — original bytes

**Mathematics and original target: approve. Source quality: request changes.** I found no mathematical gap, hidden hypothesis, weakened target, or fake definition in the complete finite proof route. Four small source-quality changes remain below. This is a nonauthor automated-agent review, not an independent Lean/Comparator rerun, human peer review, or publication acceptance.

The review covers the complete original Jordan-block ideal/worst-case GMRES equality, not a foundation or selected examples: all **50 frozen contracts**, every concrete definition, and **all 56 modules** in the actual local entrypoint closure. I read the full canonical README, retained solution manuscript, finite-route documents, source files and successful-origin raw logs. Peer findings and reports were not read. The immutable snapshot was sealed before the parent began repairs, and this verdict applies only to those original bytes.

## Canonical meaning and adversarial mathematical review

The target has not moved: the matrix is the upper Jordan block with ones on its first superdiagonal, n >= 2, a nonzero arbitrary complex eigenvalue and every 1 <= k < n. Polynomials and starting vectors are complex. The coefficient space is Mathlib's actual exponent-two Euclidean space, matrix action is the actual Euclidean matrix linear map extended continuously, and the operator norm is the continuous linear map norm. `aeval` is the usual polynomial evaluation algebra homomorphism. The infima/suprema are defined from norm value sets, and independent attainment proofs turn them into precisely the minima/maxima in the original question. The final theorem includes witnesses and comparison inequalities, so equality cannot be an artifact of a totalized empty or unbounded infimum.

I checked the pinned Mathlib definitions of these spaces, matrix maps, operator norm, polynomial evaluation, finite-dimensional continuous extension, roots/reflection, and the relevant compactness, separation, nearest-point and Rayleigh APIs. Copied source bytes equal the pinned Git objects. Canonical README/manuscript bytes also equal their recorded upstream Git objects.

The algebraic foundation includes zero dimensions, zero polynomials, coefficient truncation, Toeplitz multiplication and both orders of a finite inverse. Norm attainment and the full Gram-kernel characterization are actual spectral statements, rather than definitional assumptions. Schur recursion decreases dimension, handles unit scalar endpoints, establishes the strict inverse/energy reduction, and reconstructs all eleven supplied-data clauses, including disk denominator nonvanishing, coprimality, interpolation, the complete maximal singular subspace and its dimension. No Schur/interpolation theorem is an oracle assumption.

The weighted factorization is complete over the complex numbers. Fourier coefficients use the correct u-v sign. Effective frequency zero is allowed. Roots are multisets and retain multiplicity; zero and circle roots are treated explicitly, inside/outside counts are proved, and the proportionality constant becomes a positive real scalar before its square root is used. Common unit-circle factors are removed by decreasing degree; the zero/empty and zero-weight cases remain valid. Equality on the full circle is converted to polynomial equality using a proved infinite set, not finite sampling.

Coefficient extraction preserves full complex directional inner products simultaneously. Consequently the actual gradient image is compact and directly convex, without replacing it by its convex hull. The real separating functional gives coefficients ell(e_j)-i*ell(i*e_j), which match the complex inner product convention and the sign in T-epsilon*D. The descent proof establishes a real quadratic estimate with a genuine positive gap only on a nonempty compact complement; its empty-complement branch has its own step. At a minimizing residual this would contradict the true operator norm minimum, yielding a common orthogonal maximal vector.

Finite-dimensional closed ranges give both affine minima without an independence or injectivity hypothesis. The positive residual case uses full complex orthogonality and Pythagoras, while the zero residual case supplies an explicit unit witness. Finally, all normalized degree-k polynomials are parameterized in both directions, the reversal permutation transports pointwise action and operator norms to the exact upper Jordan block, and the final canonical conclusion keeps all original parameters. No divisibility condition, eigenvalue regime, real-only specialization or matrix doubling is substituted.

## Computation, statements and actual evidence

All thirteen frozen inputs remain unchanged. All fifty literal full statement headers occur exactly once in the independent Challenge and once in the implementation, with the recorded hashes. The Challenge contains exactly fifty intentional specification holes; it is not imported by the proof closure. There are no implementation holes, custom axioms, unsafe/native evaluation, hidden evaluator commands or kernel/resource/linter suppression in the reviewed closure. Literal header matching is a source audit; it is not a substitute for the unrun final Comparator.

Numerical work is minimized to one exact positive-half certificate using `interval_decide (trust := kernel)`. Its result is actually used in `half_min_bounds`, then the descent bounds and the final minimax dependency route. Everything substantial remains symbolic. I inspected the pinned LeanCert kernel branch and trust collection rather than assuming the command's name guaranteed kernel checking.

Actual local evidence is the coordinator's macOS serial compilation, not a run performed by this referee. The exact final receipt lists 56 successful closure modules, one compiler process, one thread and a 4096 MiB memory cap. I recursively checked 254 reuse links across 54 retained receipts and assemblies, authenticating source hashes, dependency-output hashes, successful-origin exit codes, raw logs and outputs. Every contract has a source-bound `#print axioms` and `#assert_trust kernel`; the actual final entrypoint log lists all fifty, with only `propext`, `Classical.choice` and `Quot.sound`. A successful reused module may come from a run that failed elsewhere; the packet retains that distinction per module.

The read-only verifier passed before sealing both on the immutable packet and with all original external source/output/binary bindings required. The machine-readable report gives the precise commands and counts. It does not invoke a compiler, network, subprocess, Git mutation or cache write. The retained actual42 specification elaboration log has fifty expected `sorry` warnings and is classified only as statement elaboration. The initial warning-parser quote mistake and its corrected count are documented; actual Lean bytes did not change.

**Final non-root GitHub Linux Comparator, independent default-kernel checker, sandbox/rejection checks and an exact-published-commit rerun are unrun.** The historically statement-stage metadata is pending a recorded packaging continuation. This packet contributes no complete-target count increment.

## Required source-quality changes

### R1 — reuse (request_changes)

`NLA/IE02/JordanTransport.lean:29`: Private euclidean_mul_apply exactly duplicates the public euclideanLin_mul_apply in the same submitted closure. Import SchurEnergy, remove the private duplicate, and use euclideanLin_mul_apply at the consumer currently on line 78. No frozen contract changes.

### R2 — reuse (request_changes)

`NLA/IE02/Proof.lean:10`: The entire module only forwards import CanonicalJordan and options; it supplies no mathematical declaration. The frozen inputs do not require this intermediary. Remove the forwarding-only Proof module and import CanonicalJordan directly in Solution, retaining all fifty print/assert commands. Root had separately announced this planned cleanup before the referee rechecked these exact original bytes.

### Q1 — proof-quality (request_changes_minor)

`NLA/IE02/SchurEndpoint.lean:52`: The undocumented show block reproves 0<=1 with norm_num solely to provide a type. Use (zero_le_one : (0 : ℝ) ≤ 1).

### Q2 — proof-quality (request_changes_minor)

`NLA/IE02/AffineMinima.lean:40`: The show conversion relies on S being range L without a local explanation of the witness. Add the explicit range-witness explanation or use a typed local have hd : L d ∈ S := ⟨d, rfl⟩.

These findings do not invalidate the mathematics. R1 is a within-submission public/private duplication; R2 is a forwarding-only scaffold. The original frozen contracts remain valid and need no change. Root separately announced its intended R2 cleanup before I rechecked that module and the exact frozen boundary; no peer report or finding was consulted.

## Tau Ceti standards, reuse, generality and attribution

I applied the pinned correctness, generality, proof-quality, reuse and attribution rubrics within this project. The substantial finite Schur, factorization and descent proofs contain explanatory structure and genuine intermediate API consumers. Original frozen hypotheses retained despite a stronger proof are not made artificially relevant; documented unused assumptions are a statement-boundary matter, not a reason to weaken or silently alter the canonical contract. The actual within-diff duplicates and two avoidable `show` sites are listed above.

Targeted pinned Mathlib searches covered new declaration names, the main Toeplitz/Schur/GMRES/factorization concepts, norm attainment, finite-dimensional range minima, reflection, roots, coefficient sums and polynomial intertwining. The supplied source already reuses the pertinent matrix, Rayleigh, compactness, separation, root, polynomial and finite-dimensional APIs. A broad substring search was too noisy, was not relied on, and was replaced with an exact-declaration query; both facts are retained. No TauCeti mathematical-library checkout was available or searched, so this is not an exhaustive cross-library nonduplication certification. The pinned TauCetiReview standards themselves were read in full.

All reviewed source headers retain George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, and substantial Codex assistance. Original problem/special-case attribution to Tichý, Liesen and Faber, related approximation and Courtney–Sarason background, and Mathlib/LeanCert authorship remain. No email address appears in the reviewed Lean sources. No new historical-priority claim or external-human review is implied.

## Exhaustive contract review

Each row records a separately read full statement and proof. Exact source/header hashes and all original module/output/log hashes are in `REVIEW.json` and `AUDIT.json`; the immutable full types remain in the snapshot, not shortened replacements.

| Contract | Source location | Independent mathematical assessment |
|---|---|---|
| `coefficient_roundtrip` | `NLA/IE02/Coefficients.lean:29` | The finite coefficient sum is inverse to the exponent-two coefficient vector; high coefficients are excluded only with the stated degree bound. Dimension zero and the zero polynomial are retained. |
| `coefficient_inner_product` | `NLA/IE02/Coefficients.lean:60` | The sum is the actual complex Euclidean inner product, conjugate-linear in the first argument. It is not merely equality of real parts. |
| `toeplitz_action` | `NLA/IE02/Toeplitz.lean:22` | The explicit lower diagonal entries give exactly coefficient convolution followed by truncation; finite-index arithmetic includes empty dimensions. |
| `toeplitz_algebra` | `NLA/IE02/Toeplitz.lean:131` | The matrix polynomial algebra map preserves addition, multiplication, scalars and identity. Nilpotent shift truncates precisely at n; multiplication order and finite inverse consumers agree. |
| `nilpotent_inverse` | `NLA/IE02/NilpotentInverse.lean:22` | The supplied nonzero scalar and zero constant coefficient give a nilpotent remainder. A finite geometric sum proves both inverse orders, with no inverse oracle or convergence assumption. |
| `euclidean_norm_attainment` | `NLA/IE02/NormAttainment.lean:18` | The operator norm is genuinely attained on the nonempty Euclidean unit sphere in positive dimension, using compactness and continuity. |
| `maximal_space_norm` | `NLA/IE02/MaximalSpace.lean:19` | The Gram-operator kernel is equivalent to equality in the true operator norm bound. The zero vector is handled separately; the nonzero case uses the self-adjoint Rayleigh extremum. |
| `schur_diagonal_bound` | `NLA/IE02/SchurBasicNorms.lean:18` | A coordinate of the action on a unit basis vector bounds the constant diagonal coefficient by the operator norm. |
| `schur_scalar_endpoint` | `NLA/IE02/SchurEndpoint.lean:25` | When the diagonal coefficient has unit norm, the finite first-column square sum forces every remaining visible coefficient to vanish. Only proof-quality finding Q1 applies. |
| `schur_dimension_one` | `NLA/IE02/SchurBasicNorms.lean:35` | The one-dimensional endpoint supplies the complete scalar Schur pair and its maximal-space dimension, rather than assuming interpolation. |
| `schur_defect_identity` | `NLA/IE02/SchurDefect.lean:19` | The exact adjoint expansion gives the stated signed defect identity; the real scalar 1-|c|^2 and conjugations are consistent. |
| `schur_strict_reduction` | `NLA/IE02/SchurReduction.lean:64` | Strict diagonal modulus supplies a two-sided finite inverse. The energy identity gives contractivity and an actual norm-attaining vector gives boundary norm one for the reduced matrix. |
| `schur_active_block` | `NLA/IE02/SchurActiveBlock.lean:71` | The shifted active block removes the leading zero output and trailing input coordinate exactly; both norm directions and Toeplitz structure are proved. |
| `schur_pair_step` | `NLA/IE02/SchurPairStep.lean:93` | All eleven clauses of the larger supplied-data Schur pair are proved, including degrees, disk denominator nonvanishing, coprimality, interpolation, full kernel description, action and finrank. |
| `finite_schur_boundary` | `NLA/IE02/FiniteSchur.lean:21` | Induction strictly decreases n, with scalar/unit endpoints. Existence of Schur data and the entire maximal kernel are established without a Schur or Caratheodory-Fejer oracle. |
| `scaled_maximal_factorization` | `NLA/IE02/ScaledFactorization.lean:32` | Positive operator norm is divided out and then restored. The scale, maximal kernel and complex action all use the actual matrix norm. |
| `reflection_algebra` | `NLA/IE02/Reflection.lean:27` | Fixed-bound reflection and conjugation agree with Mathlib reflect; its behavior above the bound is explicitly controlled by the hypotheses. |
| `reflection_product` | `NLA/IE02/Reflection.lean:52` | The reflected product uses the sum of the two valid degree bounds. No unjustified general multiplicativity of reflection above its bound is used. |
| `reflection_evaluation` | `NLA/IE02/Reflection.lean:59` | On the nonzero unit circle, reciprocal conjugation and the degree power produce the exact evaluation identity. |
| `circle_polynomial_uniqueness` | `NLA/IE02/CircleUniqueness.lean:18` | The complex unit circle is proved infinite via an injective upper semicircle parameterization; equality at infinitely many points then gives polynomial equality. |
| `weighted_fold` | `NLA/IE02/WeightedFold.lean:19` | For every nonnegative weight, real square root scaling multiplies the squared complex norm by that weight, including zero weights. |
| `common_circle_root_reduction` | `NLA/IE02/CommonCircleRoot.lean:19` | Vanishing of a sum of nonnegative squares forces a common root. Each polynomial is divided by the same linear factor; the degree parameter decreases only after proving it positive. |
| `fourier_semantics` | `NLA/IE02/FourierSemantics.lean:18` | Finite coefficient expansion gives the u-v frequency sign, conjugate symmetry, the degree band, and the evaluation identity. Nonzero input supplies a positive zero coefficient. |
| `effective_factor_polynomial` | `NLA/IE02/EffectivePolynomial.lean:18` | The actual maximal nonzero Fourier frequency ell controls both extreme coefficients and degree 2*ell, self reflection and unit-circle evaluation. The ell=0 case is retained. |
| `reciprocal_root_pairing` | `NLA/IE02/ReciprocalRoots.lean:53` | All roots are a multiset, preserving multiplicity. Reciprocal conjugation pairs roots after excluding zero and unit-circle roots from the strict positive circle data. |
| `reciprocal_inside_factor` | `NLA/IE02/InsideFactor.lean:57` | Inside and outside root multisets are complementary and equally sized. The complete complex factorization has the exact degree and scalar, including empty roots. |
| `strict_scalar_factorization` | `NLA/IE02/StrictFactorization.lean:24` | The complex proportionality scalar is evaluated at z=1 and proved positive real before taking its square root. The resulting polynomial has the required degree and all-circle squared norm identity. |
| `weighted_scalar_factorization` | `NLA/IE02/WeightedFactorization.lean:72` | Induction removes every common circle factor; the strictly positive remainder uses the full root factorization. Zero/empty families and zero weights are included. |
| `weighted_coefficient_preservation` | `NLA/IE02/WeightedCoefficients.lean:63` | Coefficient extraction of fixed-degree reflected products preserves every full complex pairing, not only squared norms or real parts; truncation handles high-degree directions. |
| `maximal_complex_preservation` | `NLA/IE02/MaximalPreservation.lean:23` | The full Schur kernel representation and weighted factorization construct one unit maximal vector preserving all complex directional inner products simultaneously. |
| `gradient_compact_convex` | `NLA/IE02/GradientConvexity.lean:21` | The actual gradient image of the compact nonempty unit maximal set is compact; direct two-point preservation proves real convexity of that image itself, without substituting a convex hull. |
| `real_separator_complex_form` | `NLA/IE02/RealSeparator.lean:19` | A real continuous functional on complex coordinates is represented with coefficients ell(e_j)-i*ell(i*e_j). This matches the inner product convention and later descent sign. |
| `gradient_strict_separation` | `NLA/IE02/GradientSeparation.lean:22` | If zero is absent, strict separation of the actual closed compact convex image yields one complex direction and a uniformly positive real margin. |
| `half_certificate` | `NLA/IE02/Numerical.lean:17` | The exact positive-half statement is proved by the one explicit interval_decide invocation in kernel mode and is consumed in the descent positivity proof. |
| `descent_step_bounds` | `NLA/IE02/DescentSteps.lean:25` | The explicit half-times-minimum steps are positive and bounded by one and the required ratios. All denominators contain positive +1 terms; no numerical subdivision is used. |
| `descent_quadratic_expansion` | `NLA/IE02/DescentQuadratic.lean:17` | The real quadratic norm expansion has the negative 2*epsilon cross term and correct epsilon^2 contribution, matching T-epsilon*D. |
| `descent_complement_gap` | `NLA/IE02/DescentGap.lean:18` | A gap is extracted only when the compact complement is nonempty, from a genuine maximum strictly below the maximal norm value. |
| `descent_empty_complement` | `NLA/IE02/DescentConclusions.lean:95` | The independent empty-complement step uses uniform positive directional forms on the sphere; it does not invoke a maximum of an empty set. |
| `descent_nonempty_complement` | `NLA/IE02/DescentConclusions.lean:114` | The positive gap controls low-form vectors and the margin controls high-form vectors, with both estimates valid for the same explicit step. |
| `positive_gradient_descent` | `NLA/IE02/DescentConclusions.lean:136` | The two complement cases produce strict operator-norm decrease by applying the unit-vector estimate at an actual norm-attaining vector. |
| `minimizer_orthogonality` | `NLA/IE02/MinimizerOrthogonality.lean:20` | A nonzero minimizing Toeplitz residual cannot have a gradient image excluding zero: the actual strict descent would contradict its minimizing property. The perturbation coefficient sign is -epsilon*c. |
| `affine_operator_minimum` | `NLA/IE02/AffineMinima.lean:54` | Finite linear-combination range is a closed finite-dimensional subspace of continuous linear maps with the actual operator norm; nearest-point existence supplies an attained infimum even with dependent directions. |
| `affine_vector_minimum` | `NLA/IE02/AffineMinima.lean:60` | The same finite-dimensional nearest-point argument in the actual Euclidean vector space gives an attained inner minimum for every vector, including zero. Only proof-quality finding Q2 applies. |
| `affine_minimax_attained` | `NLA/IE02/AffineMinimax.lean:95` | Zero residual and positive residual are separate. In the positive case, full complex orthogonality and Pythagoras provide one common worst vector and matching attained affine minima/maxima. |
| `jordan_reversal` | `NLA/IE02/JordanReversal.lean:53` | The explicit reversal permutation is involutive and norm-preserving and conjugates the canonical upper Jordan block to the lower one; finite-index endpoint and empty-dimension cases are valid. |
| `jordan_direction_toeplitz` | `NLA/IE02/JordanDirections.lean:17` | Every power of the lower Jordan block is a lower Toeplitz matrix by the already-proved algebra, with no restriction on the complex eigenvalue. |
| `normalized_polynomial_residuals` | `NLA/IE02/PolynomialResiduals.lean:79` | Every complex polynomial with degree at most k and constant value one is represented by precisely k free complex coefficients and conversely; k=0 is retained. |
| `jordan_polynomial_transport` | `NLA/IE02/JordanTransport.lean:60` | Polynomial intertwining preserves multiplication order; actual reversal isometry gives pointwise action and both operator-norm inequalities. Reuse finding R1 affects only the duplicated helper. |
| `gmres_extrema_semantics` | `NLA/IE02/GMRESSemantics.lean:20` | Actual sInf/sSup definitions are linked to attained norm minima/maxima by exact set-range equalities. Nonempty feasible sets and bounds prevent vacuous totalized extrema. |
| `canonical_jordan_minimax` | `NLA/IE02/CanonicalJordan.lean:74` | The theorem quantifies every n>=2, nonzero complex lam and 1<=k<n for the unchanged upper Jordan matrix, complex polynomials and complex vectors. It proves equality plus all pointwise minimum/outer maximum witnesses and comparison inequalities; no divisibility, eigenvalue regime or matrix doubling is substituted. |

## Limits, preservation and continuation

- This is an independent automated-agent mathematical/source/evidence review, not external human peer review or an official Tau Ceti service report.
- The referee did not execute Lean, Lake, Comparator, an independent kernel checker, or a sandbox. Actual local compiler results are attributed solely to the authenticated copied serial-run receipts and raw logs.
- No final GitHub Linux Comparator/default-kernel/sandbox/rejection run or exact-published-commit rerun is present. No publication acceptance or complete-target count increment follows from this packet.
- SHA-256 bindings detect byte changes against this recorded packet; they are not an external attestation of compiler provenance, a guarantee against a forged entire environment, or a proof-checker replacement.
- Only original copied bytes are approved mathematically. Later edits, operational Lake registration, updated formalization.yaml and publication must receive a separately source-bound continuation; the original snapshot and review must remain unchanged.
- Pinned Mathlib and LeanCert semantic source comparisons and targeted library searches were performed. The TauCetiReview standards were read, but no TauCeti mathematical-library checkout was available or searched; no exhaustive cross-library nonduplication claim is made.
- Some reused successful module outputs originated in runs that failed on a different module. The audit follows the successful module row, exact transitive source/output bindings, and actual raw log; it does not relabel those whole runs successful or claim review of every historical failed-debug log.
- The initial overly broad name search was archived externally and not relied on. A refined exact-declaration search replaced it. The first specification-warning counter used the wrong quote delimiter; its correction and the unchanged actual raw log are recorded.
- Original packaging metadata is historically at statement stage and explicitly pending recorded packaging continuation. It is not current proof-release evidence. Optional analytic Blaschke/Hardy compression material is outside the final theorem closure and is not claimed formalized.
- Canonical README and solution.tex were independently compared with the pinned upstream Git objects; this referee did not repeat the historical public fork/priority search or independently verify every external background paper.

Resolve R1, R2, Q1 and Q2, then authenticate actual local recompilation of the changed dependency closure and obtain separately source-bound delta reviews. Retain this packet unchanged as the original-byte verdict. Record operational Lake/metadata updates without rewriting the frozen mathematical input, and complete the final Linux controls before marking the whole target accepted.

For a read-only repeat of the sealed packet audit, run `python3 verify.py` from this review directory. `python3 verify.py --sources` additionally requires the original external files and outputs to remain byte-identical; later legitimate repairs will make that stricter original-byte check fail. SHA-256 integrity is not a replacement for an independent checker run or an external attestation against a wholly fabricated environment.
