# MF-02 independent statement review

Date: 2026-09-15. Reviewer: `/root/next_elimination`, an independent AI agent.
I did not author or modify the MF-02 definitions, Challenge, numerical-target
file, or intended proofs. I authored an unrelated IE-17 statement draft.
This report adapts the repository's Tau Ceti scope, correctness, reuse and
attribution angles. It is not human peer review, official Tau Ceti endorsement,
proof-code acceptance, or a Lean verification claim.

**Source verdict: APPROVE the reviewed mathematical statement boundary.**
There is no unresolved mathematical statement-fidelity finding. The actual Linux
boundary type-check gate has not yet been inspected, and the second independent
statement review is root's responsibility. These pending gates must pass before
proof implementation is authorized. Any change to mathematical definitions or
Challenge signatures reopens this source approval.

## Evidence read

I independently read the entire canonical README and complete source proof note
`matrix-functions-and-stability/MF-02/{README,solution}.md` at immutable upstream
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`, including every section, all endpoint
cases and attribution/scope limitations. I also inspected the generated TeX
version. The source SHA256 values exactly equal those listed by the author:
README `b779c356388860ddeab25dc9b6f35d968b6f42625c598038fa402e6841b477c9`;
solution `e104a785ddecbec117f6dffe58110222550dd7f1354bfda8c67c37daa68c1924`.

I read the complete proposed `NUMERICAL_TARGETS.md`, `NLA/MF02/Definitions.lean`,
`Challenge.lean`, Comparator declaration list, dependency boundary and draft
status. `INPUT-HASHES.json` records all exact inspected package hashes. Principal
boundary hashes are:

- Definitions: `905203d0f31ea8f28f1fcba791efe54684897df0e6df76358b3783351a51d771`
- Challenge: `7731b4023acf5747a6d08bdb9f0fd3b180199cdbcef946cd66dde21825cae611`
- Numerical targets: `3a978022d54763b5fa1b5be85d18c9e925b5a7cf8bb14d3ce679efb804ed9b6a`
- Comparator: `2bfa63c3696e91b92207af8b95e0c82cba1a512916ac9fe6a8a89688989443f7`

I inspected the pinned Mathlib definitions/API for `Submodule.span`, `Real.sign`,
`WithTop` infimum including `sInf ∅ = ⊤`, the ENat/WithTop relationship, and
`Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`. The last
lemma really permits derivative order zero and controls the exterior evaluation
under the stated degree and whole-interval boundedness assumptions. Applying it
to a polynomial and its negative gives the required absolute-value comparison;
the intended use is not a misread derivative-only theorem.

## Full-target and model fidelity

The canonical problem asks for asymptotic dependence of the true stage minimum
on arbitrary natural multiplication budget m and real gap 0<δ<1. The draft
includes m=0 and m=1, both closed input intervals, unrestricted real coefficients,
the ordinary real sign function, and one polynomial identity rather than a
fixed-size matrix minimal-polynomial shortcut. No rational-gap or fixed-gap
assumption is added. The final theorem gives absolute constants 1/4 and 1 over
the whole domain, so it remains uniform when δ varies with m.

`ProductHistory` is an honest inductive record of product gates. It starts from
1,X, retains every old register, and permits each multiplication operand and
final output to be any finite real linear combination of available registers.
This exactly accounts for free linear combinations and stored-value reuse.
Its count includes redundant scalar-product gates, but that cannot change the
at-most-budget output class: such products already lie in the free linear span
and can be omitted. Conversely a canonical straight-line program can inline
free linear combinations into the next operands and its output. No variable is
smuggled into scalar coefficients and no division or comparison primitive appears.
Degree growth is a theorem obligation rather than a hidden assumption.

`CubicComposition` allows exactly T successive real odd cubics with arbitrary
coefficients and an identity empty composition. Degenerate zero or linear stages
are admitted as in the source. The successor applies its new cubic outside the
old composition. The actual formula `a*p+b*p^3` is exactly substitution of p into
that cubic. Two-product computational inclusion and the degree bound are explicit
exported obligations. The final scalar centering belongs in the last stage for
T≥1; the draft does not silently rescale the T=0 composition.

`uniformError` is the real supremum of the actual pointwise absolute-error image
on both intervals. The maximum contract proves existence and bounds every domain
point, preventing misuse of an empty or unbounded real supremum. Each coefficient
optimization is an infimum over its full honest polynomial class; its positive
lower bounds and nonempty competitors must be proved, and no minimizer is assumed.
`stageMinimum` uses WithTop naturals, preserving the canonical infinity value for
an empty admissible stage set. Its attainment contract proves a finite admissible
stage and excludes all smaller ones. The coefficient infima are not incorrectly
asserted to attain minima.

## Constants, strictness and proof feasibility

The degree lower bound correctly quantifies over every polynomial, including
nonodd and zero polynomials, and every integer D≥1. The intended odd-part
symmetrization can only decrease the full two-interval error; squaring produces a
polynomial in x² of degree at most D, as required for the Chebyshev transformation.
The e≥1 and e=0 cases and positive denominators are explicit obligations.

The optimized cubic's scale and endpoint value match the source. Its all-x
interval theorem includes the two endpoints and the interior maximum. The
proposed exact factor identities replace interval computation without shrinking
the domain. I independently expanded the claimed quartic-residual identity using
small integer coefficient arithmetic; both sides have coefficients
`[11, 6, -15, -4, -15, 6, 11]`. The quartic factor has all positive coefficients
and positive constant on [0,1]. The positivity premises before squaring and
normalizing remain in the proof obligations.

The lower cubic-error bound includes T=0; the centered constructive upper bound
properly starts at T≥1. Strict decrease is asserted for the true infima, with an
explicit approximation/epsilon argument required. In particular a claimed
optimizer is not assumed to convert e↦e² to C_(T+1)≤C_T². At m=1, odd
symmetrization of arbitrary degree-two output is explicitly needed to obtain
E1=E0; a weaker degree-two lower bound alone would not prove that equality.
The floor bound, finite minimum and the two small-budget exceptions agree with
the complete source theorem.

These statements are substantial proof work, but they have a complete sound
source route. No vacuous predicate or target conclusion is included as a field
or premise of a custom structure. I found no statement requiring correction.

## Trust, attribution and limitations

Comparator lists all 13 Challenge declarations exactly, contains no replaceable
definitions, and permits only the three repository-approved axioms. A source
check found 13 intentional placeholders confined to Challenge, no Solution
module, and no theorem/lemma/custom-axiom declarations in Definitions. This is
not a proof of elaboration or actual axiom closure; the actual Linux build,
LeanCert kernel assertions, default-kernel replay and sandboxed Comparator with
negative controls remain required.

The draft uses George Stepaniants's full Caltech CMS affiliation without his
email and retains Chen-Chow and Cheon-Kim-Kim credit. It accurately limits the
result to the canonical uniform asymptotic order, without claiming the exact
minimum count, optimal leading constant, or stronger same-budget error question.
Those limitations match the retained solved page and do not weaken its literal
target. A later `formalization.yaml`, source correspondence, final independent
proof reviews and complete publication evidence remain necessary.

No local Lean/Lake process, dependency download, Git mutation, workflow, push or
publication was performed by this reviewer. This immutable report is a source
approval only, and can be followed by a separate actual-Linux-evidence addendum.
