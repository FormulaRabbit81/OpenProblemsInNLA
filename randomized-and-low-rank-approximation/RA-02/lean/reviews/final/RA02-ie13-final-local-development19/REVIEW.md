# RA-02 final full source and local development review

**Verdict: APPROVED for the exact complete proof-source candidate and its
source-bound local development evidence.** No mathematical, statement-fidelity,
or trust-boundary correction is required. Fresh canonical Linux verification,
Comparator and controls, and publication-commit acceptance remain pending.

Reviewer: `/root/ie13_continuation`. The RA-02 implementation authors are other
agents (`/root/mf22_publication_referee`, `/root/mi04_independent_referee`, and
`/root`). I authored no RA-02 proof source. I previously supplied independent
mathematical, API, statement-continuation and repair reviews, so this is a
continuation with that disclosed context, rather than a new blind review. I
read every selected source in full, including previously reviewed files; exact
hashes also connect this report to the earlier scoped reviews. I executed only
the attached Python evidence audit and read-only Git operations, not a compiler,
Lean, Lake, cache command, Comparator or an independent proof rerun.

## Exact reviewed scope

`SELECTED-SOURCE-PATHS.json` identifies all 34 mathematical source files plus
the `Complete` wrapper (3,009 lines). The wrapper is represented as
`Solution.lean` in the accepted-source map and as `NLA/RA02/Complete.lean` in
the local build. Its actual import graph reaches all 34 mathematical files,
contains no Challenge import, and introduces no assumptions or alternate
definitions. All 27 public theorem headers equal their frozen Challenge
headers after whitespace normalization only. The nine frozen files and ten
dependency pins are unchanged. The historical frozen planning documents
retain their original pre-implementation status wording; they are not runtime
receipts or current publication metadata.

I read the complete canonical RA-02 page and complete Colbrook manuscript.
Both raw sources were independently compared with their literal Git blobs at
`ce47b5630bf3680d9211131c3a43825b022c139a`. The manuscript copy used for displayed
reading is explicitly contact-redacted; it has its own different digest. Raw
contact material is neither copied into this review nor published.

The original universal assertion has real constants `C > 0` and `p >= 0`, then
all dimensions `n >= 1`, all complex Hermitian PSD matrices, and all integer
`1 <= r <= n`. It bounds the expected residual trace after exactly `r`
diagonal-proportional Cholesky pivots by `C*r^p` times the actual eigenvalue
tail. The final theorem negates this assertion in full. The finite arrowhead
construction establishes the sufficient lower factor `2^r/3`; it does not
claim the manuscript's sharper limiting factor `2^r`, positive-entry or
correlation-matrix extensions, or the separate RA-03 LU results. That narrower
intermediate estimate still resolves the complete original RA-02 target.

## Complete mathematical review

| Files, including all intervening helpers | Findings |
| --- | --- |
| Definitions, Parameters, Numerical | Definitions are concrete. The matrix scalar field is complex, trace is its real part, quadratic value uses conjugation, and squared norm is the Euclidean sum of complex norm squares. `PolynomialTraceFactor` has the original quantifier order. All rank-dependent parameters are symbolic and positive where needed. |
| PivotAlgebra, PivotKernel | The rank-one update is the actual entry formula. PSD preservation follows from an explicit congruence identity, not from a custom assumption. For nonzero PSD residuals, real trace is positive and masses are the required diagonal/trace ratios. Zero diagonals have zero mass. Trace zero iff the PSD residual is zero justifies the uniform dummy-label branch. |
| PathSemantics, FiniteExpectation | Path residuals and weights recurse in chronological order. Every label function is included, including repeated and zero-probability histories. The finite law is nonnegative and normalized for every length; conditional expectation recursion is proved. Dummy labels after a zero residual leave residual and error zero. No independence of successive pivots is assumed. |
| EuclideanBridge, OrderedSpectrum, RayleighMinimum, SpectralTail | The tail uses genuinely decreasing `eigenvalues₀`, with the arbitrary eigenbasis reindexing kept separate. Trace and actual nonzero eigenvectors are connected to these values. The Rayleigh proof uses the actual symmetric operator and bounded-below quotient infimum; its norm is the Euclidean norm, not the function sup norm. PSD nonnegativity, full-rank empty tail and the single last eigenvalue at dimension `r+1` are established. |
| ArrowheadEntries, ArrowheadQuadratic, StateConstruction, ProbeValues, ArrowheadTail | The complex quadratic form is exactly a positive sum of squares. This proves actual complex positive definiteness of the witness, not just diagonal positivity. The explicit nonzero probe has exact energy `epsilon^r` and norm squared at least one. Genuine spectral and PD results give a strictly positive actual tail bounded by `epsilon^r`. |
| PivotCommutation, StateUpdates, HistoryLabels, DistinctHistory | Both zero-padded state formulas are proved to follow the actual update. The two-pivot identity has the necessary nonzero denominators; active pivots are strictly positive. Every distinct history has the stated remaining-label state, not only the binary histories used later. |
| HistoryProducts, StatePotential, HistoryCardinality, StateTrace, DistinctTrace, HistoryIdentity | The product identity uses chronological actual pivots and actual prefix traces. Positivity of those traces is proved before division. The auxiliary potential is not defined to be trace: it equals actual trace in the precisely proved one-label-left case. In particular, the false empty state is not incorrectly assigned its auxiliary potential as trace. The resulting contribution formula uses actual normalized path probability. |
| CarryEncoding, RetainedCombinatorics | The two choices at stage `s` are distinct unselected labels. The carry/prefix-set invariant proves no repeated label, exact state shape, and injectivity of all `2^r` binary paths. Empty histories, `r=0` auxiliary definitions, `s=0`, and terminal `s=r` are covered. |
| FutureEstimates, RetainedTrace | Bounds hold for every `r>=1` and prefix `s<r`, including rank one. The exceptional false-state diagonal is bounded after the missing ordinary diagonal has been cancelled. Positive denominators and power directions are justified. The proof bounds the actual residual trace, never a surrogate potential. There is no terminal-prefix bound silently used at `s=r`. |
| RetainedContribution, ExpectationLower | The trace-product bound is transported across the actual finite index equivalence, then identical diagonal products cancel. Each retained path has the stated contribution. Their sum lower-bounds the full expectation because all omitted contributions are nonnegative; the retained paths are not renormalized into a different probability law. |
| ExponentialComparison, FinalCounterexample, Complete | The symbolic binomial estimate consumes the numerical certificate and yields the actual-tail factor. Exponential domination applies to every real exponent, not just natural ones. Positive tail turns this into a strict violation for every proposed pair `C,p`, with an explicit complex PD witness at dimension `r+1`. The final negation applies to the original universal PSD domain. |

The principal adversarial checks were zero/singular PSD inputs, the zero-trace
and zero-diagonal conventions, all histories rather than a selected law,
the genuine eigenvalue ordering and tail, complex conjugation and Euclidean
norm, positivity before cancellation, rank one, `r=n`, and arbitrary real
polynomial exponents. None exposes a vacuous premise or weakened target.

## Numerical certificate, reuse and proof quality

The only LeanCert calculation is `Real.exp 1 <= 3`, proved by
`interval_decide (trust := kernel)`. Its dependency is explicit:
`exp_one_bound -> rank_denominator_le_three -> exponential_tail_factor ->
universal_counterexamples -> no_polynomial_trace_factor`. All dimensions,
histories, eigenvalues, ranks, tiny parameters and real powers remain symbolic.
There is no interval subdivision, numerical eigenvalue approximation, factorial
history enumeration or large rational matrix expansion.

I checked the pinned Mathlib interfaces for PSD congruence, trace-zero
characterization, positive and nonnegative eigenvalues, decreasing spectrum,
Rayleigh-infimum eigenvalues, binomial/exponential comparison and real-power
asymptotics against literal pinned Git sources. This work uses these APIs rather
than assuming missing spectral or probabilistic foundations. The final observed
ExponentialComparison repair only removes the incorrect `Real.` prefix from the
existing root-namespace asymptotic theorem. Its three theorem headers and all
trust/resource settings are unchanged; the earlier failed log is retained.

The scoped Tau Ceti correctness, generality, proof-quality, reuse and attribution
rubrics were applied. This is neither an official Tau Ceti review nor a CLI run.
Generic PSD/path and Rayleigh foundations precede the concrete family. Public
contract bundles serve the frozen correspondence boundary. Some existing
lint warnings concern unused hypotheses retained by that boundary, deprecated
syntax, or redundant tactic/simp arguments. They do not affect the statements,
trust or source approval; no post-success cosmetic source change is requested.
Original mathematical attribution remains Matthew J. Colbrook, Cambridge
DAMTP; formalization credit is George Stepaniants, Caltech Computing and
Mathematical Sciences, with AI assistance and Apache-2.0 licensing.

## Independently audited actual local evidence

The attached audit completed successfully. It matches all 114 assembly input
hashes to the terminal development-19 receipt and checks every selected RA-02
source, current compiled output, direct compiled dependency hash, and transitive
source map along the reuse chain. All 35 actual original compilation commands
have exit code zero and matching retained log/output hashes. All 35 complete
origin logs were read, including the empty Definitions log.

Development 19 compiled ExponentialComparison, FinalCounterexample and Complete
afresh and reused 32 exact successful outputs. The review traces those reused
outputs to their original successful commands; it does not describe all 35 as
fresh executions in development 19. The terminal run has no failed or blocked
modules. Complete's actual log reports all 27 exports with exactly `propext`,
`Classical.choice`, and `Quot.sound`; its 27 explicit kernel-trust assertions
also completed. There are no custom axioms, proof holes, native trust commands,
unsafe declarations, or extra active resource options in the selected sources.

The evidence is local serial macOS compilation using shared pinned compiled
dependencies, with one compiler process and one thread, and a 4,096 MiB process
cap for the final run. Definitions' earlier successful origin used 3,072 MiB.
This review is an independent source/evidence audit of those actual commands,
not a second execution. It supplies no fresh Linux kernel export/replay,
Comparator equivalence or rejection/sandbox-control result. Those canonical
gates, exact publication rerun, and upstream PR review must still be completed.
No repository status, publication commit, PR or verification count was changed.
