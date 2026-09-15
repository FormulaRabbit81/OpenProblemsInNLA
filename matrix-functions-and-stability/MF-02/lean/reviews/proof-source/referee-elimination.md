# MF-02 independent full proof-source review

Reviewer: `/root/next_elimination`, an independent AI agent, 15 September 2026.
I did not author or edit any MF-02 definition, Challenge, proof, or packaging
file. My IE-17 implementation is separate. This review adapts the repository's
Tau Ceti scope, correctness, proof-quality, reuse, and attribution standards;
it is not an official Tau Ceti review or external human peer review.

**Mathematical source verdict: APPROVE the complete intended proof route and
all thirteen frozen target signatures.** I found no mathematical scope defect,
vacuous premise, false certificate identity, or missing optimization bridge in
the reviewed source. This does not certify Lean elaboration: the actual Linux
module builds, axiom closures, default-kernel replay, Comparator, and final
compiled-source addendum remain required. I inspected no Linux log for this
report and claim no mechanical acceptance.

The immutable inspected files and exact SHA256 hashes are in `CHECKS.json` and
`source/`. I read Definitions, Challenge, all nine helper/proof modules, and
Solution in full, including the entire Chebyshev, cubic, and infimum arguments.
I compared them with my prior independent full canonical-source review at
upstream `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`; that earlier report records the
complete README/solution-note hashes and primary Mathlib API inspection. The
Definitions and Challenge bytes are unchanged from my approved statement
boundary. All thirteen implementation signatures match Challenge exactly after
whitespace normalization. No proof-source placeholder, custom axiom, native
decision tactic, or Challenge import was found by a supplementary lexical
scan; actual transitive closure must still be checked mechanically.

`Model.lean` proves degree growth by induction on actual product history, then
extends the register bound to every free real linear combination. Each product
retains all older registers. Cubic inclusion explicitly computes p² and p³ in
two new gates while reusing p and the square, and forms the final output freely.
Neither formula-tree recomputation nor an assumed degree-as-cost definition is
substituted for the shared-register model. The exact-T composition includes
degenerate linear stages; final scalar centering is absorbed only when T>=1.

`Errors.lean` proves compactness separately on the positive and negative
closed intervals, where Real.sign is constant, and obtains an actual attained
maximum. All interval endpoints are retained. Both coefficient-infimum classes
are nonempty via X and bounded below by zero; the lower and upper sInf rules
are applied to these honest classes. There is no totalized empty-supremum
shortcut and no assumed optimal coefficient tuple.

`Parity.lean` takes the true odd part of an arbitrary real polynomial and
bounds its positive-interval error using both original intervals. Evenness of
the odd part squared implies exact expansion from a polynomial in X², with
degree at most the original degree and value zero at the origin. Thus the
subsequent Chebyshev argument covers nonodd, zero, and lower-degree inputs.
`Chebyshev.lean` transforms [δ²,1] to [-1,1], obtains a polynomial bounded by
one everywhere there, and evaluates it at the exterior point γ that maps back
to zero. The imported Mathlib exterior comparison is used at derivative order
zero, within its true degree and full-interval hypotheses. The Joukowski value
is proved by exact recurrence, not an unproved exponential/asymptotic formula.
The scalar inequality gives r^D<=e for every strict tolerance between the
actual maximum and r^D. This avoids assuming a positive attained error or
discarding the e=0 case.

`Cubic.lean` controls the whole interval through two exact positive-factor
identities, including its interior maximum and both endpoints. The critical
point is positive and strictly between a and 1. Positivity is established before
squaring or clearing denominators. I independently reexpanded the sixth-degree
gap-ratio factor identity: both sides have coefficients
`[11,6,-15,-4,-15,6,11]`. The displayed quartic factor is positive on [0,1].
The resulting new ratio bound is uniform for every real 0<a<1. No sampled
interval list, rational-gap restriction, or numerical root enclosure replaces
that quantifier.

`Iteration.lean` composes these interval maps for arbitrary T and centers the
last stage while preserving the exact stage count. Its error-improvement lemma
handles T=0 without improperly adding a preliminary scaling gate: the scaling
is incorporated into the new cubic coefficients. Its crucial square-step
argument chooses e strictly between the current infimum and
min(1,sqrt(C_next)), then extracts a polynomial with error below e by the
defining infimum. The contradiction proves C_next<=C_current² without an
optimizer assumption. T=0 strict decrease is handled separately; for positive
T the lower degree bound supplies C_T>0 and the constructive bound supplies
C_T<1, so squaring gives genuine strict decrease of the actual infima.

`Bounds.lean` preserves both small multiplication budgets. For all m<=1,
the program-degree bound is at most two, and odd symmetrization removes the
quadratic coefficient, giving a degree-one lower bound. A free centered linear
polynomial attains the matching bound, so E_0=E_1=r. Class inclusion uses the
actual two-product cubic program to give E_m<=C_floor(m/2), not merely a degree
comparison. `Minimum.lean` exhibits a finite admissible stage, uses Nat.find
to prove the exact WithTop infimum is an attained natural minimum, and excludes
every smaller stage. For m>=2, strict decrease and class inclusion yield the
floor(m/2) lower bound, while the matching r^(2^m) lower/upper error bounds give
T<=m. The m=0 and m=1 minimum is exactly one. These facts prove the final
uniform constants 1/4 and 1 for all m and all 0<δ<1, including arbitrary
dependence of δ on m.

The code avoids expensive interval computation through exact factorization,
recurrences, free-span induction, and order/compactness arguments. Reuse of the
pinned Mathlib Chebyshev and polynomial APIs is appropriate; no independent
Chebyshev extremal theorem is reimplemented. Polynomial and natural-number
abstractions match the canonical scalar multiplication-complexity question,
without assuming a fixed matrix's minimal polynomial.

George Stepaniants's name and full Caltech Computing and Mathematical Sciences
affiliation appear without an email. Chen-Chow's cubic and the prior
Cheon-Kim-Kim complexity results retain their source credit in Definitions;
the Chebyshev implementation credits Mathlib's contributor. The scope remains
the canonical uniform asymptotic order, without an exact leading constant or
same-budget stronger-error claim.

No local Lean/Lake invocation, workflow trigger, Git mutation, dependency/cache
download, or canonical-file edit was performed for this review. Final acceptance
must inspect the actual successful source hashes and raw mechanical evidence;
source approval alone is insufficient for a Lean-verified count or publication.
