# MF-02 independent proof-source review

Reviewer: Codex agent `/root/next_inequalities`, separate from the MF-02 authoring
agent. Date: 15 September 2026. This is an AI-agent review applying the project's
scoped Tau Ceti checks, not human peer review or a kernel-verification receipt.

**Disposition: no substantive mathematical or statement-scope objection in the
inspected source. Final verified acceptance is withheld pending successful actual
Linux compilation, LeanCert trust checks, Comparator, kernel replay and controls.**

The review did not edit any MF-02 source or run local Lean/Lake. All entries in
STATEMENT-FREEZE.json's source_hashes matched at review time. The exact reviewed
Lean-file hashes are recorded in REVIEWED-SOURCE-HASHES.json.

## Original target and semantic boundary

I read the canonical README and complete solution.md at immutable upstream
8f04b905eb2e0827b6b84f37d9d080ae1f05b202 and compared them with Definitions.lean,
Challenge.lean, NUMERICAL_TARGETS.md and all nine implementation/entry files.
The canonical target is the uniform constant-factor asymptotic order of the
actual stage minimum, including m=0,1. The final theorem preserves all natural m
and all real 0<delta<1 with no hidden endpoint separation or rational-gap premise.
The stronger exact-minimum/leading-constant/same-budget questions are correctly
excluded from the canonical claim, consistently with the unchanged source page.

ProductHistory retains old registers, and freeSpan supplies precisely free real
linear combinations. A history step creates the product of two available span
elements. Its index counts gates, while ProgramComputable permits any history
index at most the requested budget. Reuse is preserved. Scalar coefficients are
real polynomial coefficients, not input-dependent functions of the formal X.
Allowing a redundant scalar product step does not strengthen the at-most-budget
model, since such a product is already in the free span. The degree proof follows
actual history induction. The cubic cost proof explicitly retains p, computes
p*p and (p*p)*p, and forms the final free linear combination in two new gates.
This matches the source's straight-line model and introduces no branching,
division primitive, formula-only restriction, or fixed-size matrix reduction.

The error supremum ranges over both complete closed intervals and the true real
sign. Errors.lean proves the image compact and nonempty and extracts an actual
maximum; subsequent supremum inequalities use that contract. The coefficient
classes are nonempty (identity stages) and bounded below by zero. Infimum lower
bounds use a nonempty class; upper bounds use bounded-below membership. There is
no appeal to default sInf/sSup values or an assumed coefficient optimizer.
The extended-natural stage minimum retains infinity for an empty admissible set,
and Minimum.lean proves admissibility and obtains an actual least natural via
Nat.find before drawing the final comparison.

## Proof soundness and completeness

The odd-part reduction controls both signs and handles arbitrary non-odd input
polynomials. Contract/expand proves the square is a polynomial in X^2 with the
necessary degree and zero value. The Chebyshev exterior comparison is applied
only after proving the full [-1,1] bound and valid degree bound; its exterior
point is at least one. Exact Chebyshev recurrence replaces logarithm/cosh
computation. An intermediate strict tolerance handles zero error without dividing
by it or presupposing positivity of the actual maximum.

The optimized cubic uses positive scale and explicitly derives its critical
point inside the interval. The lower and upper image bounds follow exact
positive-factor polynomial identities. The ratio comparison proves denominator
positivity before clearing and squaring. Its identity is valid for every real
gap, not inferred from numerical samples.

Iteration builds every stage explicitly. Centering is absorbed into the last
stage when T>=1, with the zero-stage case preserved. For strict improvement of
the coefficient infima, Iteration.lean chooses a tolerance between C_T and
min(1,sqrt(C_(T+1))), then obtains a near-infimum polynomial with error below it.
It never assumes an optimal coefficient tuple. The lower degree bound proves
strict positivity, and the first-stage argument is handled separately.

The small-budget proof uses that the odd part of an arbitrary quadratic is
linear, rather than incorrectly identifying the whole one-product class with
linear polynomials. The lower stage bound uses actual inclusion of every
T-stage cubic composition in the 2*T-product class and strict decrease of C_T.
The upper bound compares the constructive C_m bound with the unrestricted degree
bound. Natural-floor and real-cast conclusions retain m=0,1 and yield constants
1/4 and 1 independent of the gap. These are the complete canonical conclusions.

## Trust, computation and remaining gates

I found no source occurrences of sorry, admit, native_decide, custom axioms or
unsafe declarations in Definitions or the implementation closure. Deliberate
Challenge placeholders remain only in the independent statement environment.
Solution imports only the implementation and asserts kernel trust for all
thirteen exports; Comparator requests all thirteen, no interchangeable
definitions, and only propext/Classical.choice/Quot.sound. The import dependency
graph is acyclic and contains no Challenge import into the solution.

No interval subdivisions or floating-point estimates are required: the main
numerical work is exact low-degree polynomial algebra plus a reused extremal
Chebyshev theorem. This is appropriate computational reduction for the user's
LeanCert and optimization requirements. Attribution preserves Chen-Chow and
Cheon-Kim-Kim and gives George Stepaniants his authorized department/university
credit without an email.

This report is source-level acceptance for continued checking, not permission
to count or publish MF-02 as Lean verified. Actual elaboration can still expose
API/tactic failures; those must be repaired without changing the frozen target.
Final metadata, formalization.yaml, authoritative raw receipts, controls and
independent final referee acceptance remain publication gates.
