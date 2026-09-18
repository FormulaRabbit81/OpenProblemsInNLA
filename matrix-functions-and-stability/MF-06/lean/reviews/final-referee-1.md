# MF-06 complete original-target independent source review

**Verdict: APPROVE the exact local268 mathematical proof and code source.**
There is no unresolved mathematical or source-correctness blocker in this review.
This is a full-target source approval, not a publication-package approval, a new
Lean execution by the reviewer, a Linux Comparator result, or a campaign count.
The final Linux kernel/Comparator/sandbox acceptance and publication gates remain.

Reviewer: `/root/nm04_final_referee1`, independent nonauthor. I have never authored
MF-06 candidate proof code, definitions, frozen statements or numerical targets.
My work consists of review reports and evidence verifiers. I did not run Lean,
Lake, Comparator, a network workflow, or any candidate proof-producing script.
I recorded my conclusions without reading the other final referee's verdict.
Earlier bounded reviews by this same reviewer are explicitly identified; they
were expanded here to a complete mathematical target assessment, not counted as
additional independent reviewers.

## Exact reviewed scope and standard

The source is the unchanged canonical MF-06 README and complete 296-line informal
solution, all six frozen files, all 38 contracts, and the entire 119-module local
project import closure ending in `Solution.lean`. The proof-source hashes are in
`SCOPE.json`; the source copies are in `source/`. `READ-LEDGER.json` distinguishes
complete reads during this final review from exact-source complete reads in my
previous bounded C13, C15, C17–C23, C29 and transfer reviews. All project closure
sources have personal complete-read coverage. Previously published MF05/MF07
sources retain their source pins and authorship. This is not a claim to have
reviewed every implementation in the Lean, Mathlib or LeanCert libraries.

The approved source is the immutable `MF06-local268-source-snapshot`, matching the
live candidate at review. The actual root-owned aggregate is
`MF06-LOCAL-COMPLETE-268.json`, SHA-256
`7c138cd627b595aa7e18c625cc39b73a673ed0434d6020664d77d769b2cdeaa6`.
All frozen hashes still match the pre-body `STATEMENT-FREEZE.json`. The two
statement reviews, statement elaboration and statement-first numerical plan are
retained historical evidence. The new final review does not alter their boundary.

I applied the pinned Tau Ceti reviewing guide and its correctness, generality,
proof-quality, attribution and reuse rubrics. Their exact bytes/hashes are
retained in `standards/`. This means a source review under those rubrics, not an
executed external Tau Ceti service or a certification of the reviewer itself.

## Original target and definition correspondence

C38 states, in order: every positive dimension and fixed nonempty compact complex
matrix family M; then positive r and C; then every nonempty compact N; then the
Hausdorff-neighborhood premise and the original one-sided linear lower bound.
There is no finite-family, irreducibility, product-boundedness, invertibility,
positive-reference-radius or invariant-subspace condition in C38. The result is
pointwise at M, not a uniform two-reference estimate. It is the original target.

The reused spectral norm is the norm of the actual Euclidean continuous linear
map. Chronological words are reversed-list products, so appending a letter acts
on the left. `familyGrowth` is the supremum of norms of actual words, with compact
attainment proved. `jointSpectralRadius` is the genuine root infimum; C03 proves
its equality to the all-word root limit for arbitrary radii, including zero.
The canonical Hausdorff distance is literally the max of two sup-inf expressions
in that spectral norm. C02 proves finiteness, equality to the operator-image
Hausdorff metric, both nearest-generator directions and zero-distance equality.
Consequently no total-definition behavior on empty or unbounded sets substitutes
for the canonical mathematics.

The new definitions are concrete word envelopes, an infimum, real norm bounds,
coordinate fibers, sorted minors, explicit Kronecker entries and allocation
entry products. They contain no theorem oracle. In particular, the invariant
flag, irreducible boundedness, full exterior representation, stable kernel and
perturbation estimate are proved rather than supplied as structure fields or
extra premises. C18 identifies sorted minors with Mathlib's actual exterior-map
matrix. C19 proves multiplication, identity and degree-zero behavior.

I compared all 38 literal frozen headers with their unique implementation
headers and final exports. C38's proof explicitly branches on zero versus
positive reference radius. The zero case uses nonnegativity and never divides.
In the positive case the actual scalar-image identities normalize M, choose the
constants before N, take r = r0/c, and multiply back by positive c. N need not
have positive radius in a premise. Zero Hausdorff distance and singular or zero
generators remain in scope.

## Product-bounded reference case: C05–C10

The undiscounted all-word envelope is finite by product boundedness, includes the
empty word and dominates Euclidean norm. Its complex norm laws and continuity
follow from proved word estimates. The finite-tail supremum is taken over actual
length-n words and is a continuous seminorm. The tail sequence decreases, and
its actual infimum is a continuous Mathlib seminorm. Compact-uniform convergence
is obtained from Dini's theorem, not an unproved interchange of limits/maxima or
a finite-generator approximation.

The limiting max recurrence uses actual continuous maxima over compact M and a
nested family of closed nonempty subsets of M. A single member in the compact
intersection attains the limiting maximum for each fixed vector. This addresses
the potentially invalid shortcut of letting a separately chosen maximizing
letter depend on n without extracting a limiting letter.

The kernel is the actual zero set of that seminorm. It is an invariant complex
submodule. Uniform convergence on the compact closed unit ball in the kernel
produces a strictly contracting block length. Restricted growth is the supremum
of actual unit-vector actions with zero inserted. Its submultiplicativity uses
invariance of the **reference** kernel. A symbolic N-th root of one half gives
strict exponential decay. If the kernel were all of the space, the contracting
block would contradict the radius-one all-word lower bound. The bottom-kernel
case is covered by the inserted-zero definition and vacuous unit-vector bounds.

The quotient seminorm is built by an actual quotient lift and proved definite;
it is not assumed. The stable-coordinate norm is a finite sum of actual tails.
The telescoping estimate gives contraction q = 1 - 1/(2C), with 0 <= q < 1.
An actual orthogonal projection and its complementary vector supply the two
component seminorms. Positive coercivity follows by minimizing a continuous
positive function on the finite-dimensional unit sphere. These choices also
produce a real starting vector with stable component zero and quotient norm one.
No nonzero stable-subspace premise is needed.

For the perturbation step, an actual reference generator attains the quotient
max recurrence, and compact N supplies a nearest generator. The operator error
bounds apply to both component seminorms on the entire original vector. Hence
the proof controls the perturbed lower-left block without assuming that N
preserves the reference kernel or flag. The symbolic cone inequalities preserve
a <= H b and a positive quotient component. Finite induction appends actual
chosen N-generators and produces legal words at every length. The lower radius
bound follows by contradiction with the genuine all-word exponential envelope
above the root infimum. It does not rely on periodic attainment or on one
infinite maximizing word. r and C are visibly fixed before N in C10.

## Block theory and irreducibility: C11–C16

The earlier exact C13 review covers the full scalar-sum, block-radius and
nonresonance dependency argument. Its sources remain unchanged. The separated
sum bound is a conservative finite constant, valid at n = 0 and arbitrary
0 < q < 1. It preserves the elementary prefix-cut proof while avoiding a square
root. In the two-block estimate the intervening factors come from the same
original word, including an empty gap for adjacent positions. The finite-block
induction retains grouped-prefix off-diagonal terms. Its tensor-block radius
comparison is applied to actual paired generators, not independent choices of
letters in the two blocks. This distinction is necessary and respected.

C12 proves the radius of a full triangular compact family equals the maximum of
its actual diagonal-family radii; zero diagonal radii are allowed. The proof
supplies an upper exponential envelope and passes to a rate limit, and proves
the lower bound by actual compression. No unjustified principal-compression
monotonicity is used for arbitrary nearby families.

C14 proves the needed irreducible boundedness internally. The span of all actual
word images of a nonzero vector is invariant and hence full. Compactness of
operator/vector unit spheres then turns positive pointwise tests into a finite
short-word bridging bound. If a word were too large, genuine concatenated words
would amplify every vector by a fixed factor greater than one with a bounded
length cost. Comparing with a rate arbitrarily above radius one gives a
contradiction. There is no Barabanov/extremal-norm assumption or irreducibility
oracle, and no assumption of finitely many generators.

C15 constructs a saturated common invariant chain, adapts a basis by nested
independent extensions, and gives actual two-sided inverse matrices. The literal
block coordinate map is surjective. Invariance of the induced diagonal quotient
blocks is transferred back to adjacent elements of the chain, proving their
irreducibility. Its stronger arbitrary-family statement includes empty and
infinite M. C16 uses actual same-word conjugacy with word-independent constants
to establish both radius and product-boundedness invariance. The exact earlier
C15 source review remains part of the read record, not an assumed flag theorem.

## Exterior allocation and critical degree: C17–C33

The compound dimension is the actual k-subset cardinality. The implementation
retains k = 0, k > d where stated, empty determinants and zero factors. The norm
and Lipschitz estimates use symbolic determinant expansion and finite-product
telescoping. Their dimension constants are applied to a complete word, not
repeated once per generator. They therefore disappear from radius comparisons.
Exact Hilbert tensor norm multiplicativity is unnecessary: proved entrywise
upper/lower comparisons have fixed finite dimensional constants.

C24–C26 use real block-fiber dimensions and actual allocation coordinate spaces.
Degree-zero factors have dimension one. The product-of-sums identity proves
coordinate tensor multiplication. Diagonal block multiplication requires and
uses actual triangularity in C25. C26 also works without a triangularity premise:
it multiplies the tuple of each actual diagonal-block word before forming its
tensor, rather than falsely identifying it with the diagonal of an arbitrary
full matrix product. All allocation factors still share the original letters.

I separately read the complete agent-authored C27/C31 route and challenged the
basis ordering and signs. Occupations are extracted from actual subsets of
coordinates. Explicit extraction/assembly inverses and finite equivalences
identify each occupation fiber with its allocation tensor coordinates. A nonzero
minor has a nonzero Leibniz term. Upper triangularity forces every term's row
block label to be no later than its column block label. Equal total weight then
forces equality label by label, hence equal occupations. Ordering allocations
by weight and a finite tie-breaker gives a genuine upper-block-triangular
compound matrix, with positive actual block dimensions.

The grouped minor uses separate row and column reindexings. Their determinant
signs are handled by **norm equality**, not by an unjustified unsigned matrix
identity. The determinant of the genuinely grouped triangular minor factors
into its diagonal minors, including empty factors. Explicit coordinate
bijections give norm comparisons in both directions for compound diagonal and
allocation matrices. These comparisons are applied once to complete same-word
products. Thus C27 gives the exact radius maximum, while the corresponding
paired-word comparison gives C31 the hypotheses of full block nonresonance.
There is no hidden independent-generator pairing, generic-position restriction
or division by a minor/norm that might vanish.

C28 gives strictly greater max-allocation degree for distinct equal-degree
allocations, even with coordinate ties. C29 rearranges the same row and column
coordinates in each block for max/min allocations and bounds an arbitrary P.
It covers singular P, zero entries and degree-zero factors, uses a positive
finite dimension factor, and performs no inverse or division. In C30 the lower
allocation has product-bounded words, while the higher allocation lies in a
strictly subcritical compound degree. The same-word tensor estimate therefore
yields a strict paired radius gap.

C32 proves the exact radius-power upper bound for all allowed degrees, including
zero radius and degree zero, and equality at degree one via actual singleton
coordinates. A largest critical degree exists because degree one qualifies.
C33 obtains the irreducible flag, proves boundedness of each diagonal family,
uses the full occupation decomposition/nonresonance argument, and transfers back
through actual exterior conjugacy. Neither product boundedness nor an invariant
flag of the original family is assumed as an extra hypothesis in C33.

## Transfer and boundaries: C34–C38

The exterior image-Hausdorff estimate proves both directed distances by actual
nearest generators. It does not require injectivity of the exterior map. A
common ball for nearby original families is established before applying the
minor Lipschitz constant. The C10 neighborhood and all exterior constants depend
only on fixed M and its critical degree. The neighborhood is shrunk enough for
both the C10 hypothesis and a nonnegative retained scalar lower bound.

C36 uses the integer-power inequality u^k <= u for 0 <= u <= 1, and the trivial
u >= 1 case. This avoids numerical fractional powers and preserves the exact
linear lower conclusion. C37 discharges its conditional transfer helper with
the proved C33, rather than exposing a product-bounded exterior-power assumption
in the final theorem. C38 separately handles zero radius, then exactly rescales
both radius and Hausdorff distance by a strictly positive number. The order of
quantifiers is correct at each assembly step.

## Genuine LeanCert consumption and computation minimization

The source-pinned MF05 half certificate uses `interval_decide (trust := kernel)`.
It is genuinely consumed by the cone positivity argument, the common-ball
argument and directly by the exterior transfer. It is not merely imported or
printed. The actual local270 theorem-body constant dump records paths from C38
through C37/transfer to that certificate, and the certificate body references
`LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`. The replay checks
these edges against the raw dump. No reviewer compiler run was used to obtain it.

The only certified fixed numerical value is one half. Arbitrary q, dimensions,
word lengths, compact families, determinant sums and allocation indices remain
symbolic. There are no interval subdivisions, matrix searches, brute-force
permutation evaluations or floating-point hypotheses. Conservative internal
constants, whole-word comparisons and integer-power transfer substantially
reduce computation without weakening the frozen canonical target.

## Actual local evidence and limitations

Root's actual macOS local268 run finished successfully: 119 closure modules,
with two fresh compilations (`CanonicalLower` and `Solution`) and 117 reused
source/dependency/output-matched successful results. The packet retains all 217
original provenance records/logs, not just the success summary. The read-only
verifier follows every reuse chain to its successful fresh origin, checks the
source and dependency output identities, command limits, log hashes and exact
final export scope. The actual `Solution.log` prints all 38 declarations with
exactly `propext`, `Classical.choice`, `Quot.sound`; all 38 `#assert_trust kernel`
commands are in the successfully executed source. Benign unused-premise and
style warnings remain, including frozen hypotheses. They are retained, not
reported as absent. No `sorry`, added axiom, `unsafe`, native-decision bypass,
custom elaborator or Challenge import occurs in the candidate proof closure.
The 38 intentional Challenge placeholders are kept outside that closure.

Earlier development failures remain in retained history. The final continuation
from the initially inspected local264 involved only four small implementation
corrections: removing a redundant closed-goal `rfl`, expressing allocation range
reindexing through the actual equivalence, opening the existing MF05 namespace,
and orienting positive scalar multiplication correctly in C38. Their complete
diffs and before/after source hashes are retained. No frozen header changed.
They were independently inspected rather than inferred harmless from compilation.

The actual local270 diagnostic independently elaborates the frozen Challenge
boundary and the proof import, dumps all 38 types/universe lists, and records
opaque theorem-body references. Its Challenge prefix is checked against the
original frozen bytes plus the diagnostic import only. Both original type
dumps are retained losslessly compressed; the read-only verifier recomputes
all comparisons. The earlier local269 diagnostic failed when an API call did
not request opaque bodies; that was not a proof failure or a successful
Comparator run. Local270 explicitly requests opaque values and succeeds.
This diagnostic is local Lean evidence, **not** the Linux Comparator.

The reviewer replay is ordinary read-only Python. It authenticates the reviewed
bytes and the cited records; it does not make logs impossible to forge or replace
an independent kernel run. Actual Linux Comparator, default kernel, non-root
sandbox and negative/regression controls are still separate future gates for
this exact candidate. This source approval changes no campaign count.

## Quality, attribution and final disposition

The proof uses named small modules and actual library constructions. Mathematical
bridges for reindexed minors, literal Kronecker entries, leading blocks and the
degree-one compound are explained next to their definitions or rewrites. Earlier
requested explanatory comments remain present and source-bound. The unusual
higher-order analytic and allocation steps were reviewed as mathematics, not
accepted solely because the compiler passed. No essential premise is vacuous.

George Stepaniants is credited with Department of Computing and Mathematical
Sciences, California Institute of Technology. The original Epperlein–Wirth target,
Barabanov/Wirth, Chitour–Mason–Sigalotti and Morris background, and the reused
Matthew J. Colbrook proof contributions retain attribution. Substantial AI
assistance is disclosed. No priority or external human peer-review claim is made.
No George email is added by this review.

Historical frozen files accurately describe the state when drafted; their old
"draft/unproved" text must be presented as history, not the current package
status. Current publication metadata, reproduction commands, workflow selection
and privacy of the complete eventual publication package are a separate bounded
preflight. This review neither approves unseen metadata nor delays source
approval until those independent gates.

**Disposition:** approve only the exact source map in `SCOPE.json` as a complete
mathematical/code formalization of original MF-06. No outstanding source changes
are requested. A changed proof/definition/contract requires an appropriately
scoped continuation. Final runtime and publication acceptance remain pending.
