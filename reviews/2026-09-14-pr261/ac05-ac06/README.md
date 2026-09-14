# Independent PR261 audit: AC-05 and AC-06

**PASS for the new research scopes; retain both entries as Open.** Reviewed on
2026-09-14 at PR head `9bf50028bc30e6cdf78e19089befcb9b9bd6c292`, against base
`27540c8022a33fef171625b7e48a95e33562d535`. No mathematical blocker was found in
the audited scope. The displayed original targets, fields, dimensions and
permanent IDs are unchanged. Neither manuscript proves its original target.

This is a fresh informal AI review, not human peer review or formal verification.
The complete current manuscripts, canonical notices, supplied review, and code
used below were read. Submitted code ran only in scratch copies. No source
worktree or remote state was changed by this subtask.

## Direct mathematical review

### AC-05

The three-subspace normal form and Theorem 3.2 are valid under the scalar
pair-intersection hypothesis. In the product decomposition, a private summand
can occur in only one action image; with at least two graph coordinates the
three graph words are independent. This proves the all-product assertion for
arbitrary grouped endomorphisms, rather than extrapolating from sampled powers.
The hypothesis cannot be removed, as the diagonal-tensor control illustrates.

Corollary 4.1 correctly retains the two global scalar directions and imposes
the extra sum-of-local-coefficients trace constraint for U. Consequently its
general-linear stabilizer dimension is m+2 and its special-linear dimension
is m−1; the corresponding generic F dimensions are m+2 and m. The Q dimensions
are 2m+2 and 2m. Generic classification requires every parameter to avoid 0
and −1; the exceptional −1 stabilizer calculations are separate.

Theorems 5.1 and 6.1 correctly pass from conjugacy of the entire stabilizer to
common monomial grouped maps. The distinct character configurations have only
the stated cube/product-triangle automorphisms. The six-entry coefficient ratio
cancels arbitrary grouped diagonal scalings, so parameter multisets are
preserved modulo reciprocal values. The explicit reciprocal maps prove the
converse. The arguments include arbitrary changes of basis and large-factor
permutations.

The balanced Q representatives have scalar Gram matrices and closed
special-linear orbits by [Acuaviva et al., Theorem 2.5](https://arxiv.org/html/2209.14358v1).
The projective semistable orbit-closure argument uses precisely the unique
polystable-orbit property in [Woodward, Lemma 4.2.3 and Proposition 4.2.5](https://arxiv.org/pdf/0912.1132v6).
The explicit F-to-Q limit, orbit dimensions, and multiset cancellation establish
Theorem 7.3 and the restricted-catalyst result. They do not cover arbitrary
catalysts, unequal formats or asymptotic conversion rates. Section 8's U
separation and nullcone argument respect that same scope.

The commutator inequality in Section 9 follows from a rank-r decomposition,
the rank-(r−n) complementary idempotent, and polynomial minors after clearing
the invertible slice's determinant. This extends correctly to complex border
rank. The local commutators yield either an invertible commutator in one
position or the balanced-ternary construction with exactly one zero
eigenvalue. Thus the all-power bounds are (3·3^m−1)/2 for U, F₁ and Q₁, and
(3·3^m+1)/2 for Fλ outside {0,1} and Qλ outside {0,1,−1}. Their m-th-root
limits are 3. They obstruct exact minimal-border-rank finite blocks without
contradicting asymptotic rank 3. The 27-coefficient trace realization and its
exceptional-parameter limiting construction were also checked.

Excluded from this fresh PASS: inherited upper-bound constants, the prior
dimension-three reduction, and all claims inside nested baseline archives.
None is needed for the newly audited structural and lower-bound results.

### AC-06

The CRT compactor preserves bounded integer-polynomial nonvanishing because
its factorial-based moduli are pairwise coprime and exceed each candidate
evaluation in absolute value. The construction and coordinate bit lengths
are polynomial in the numeric degree bound and other stated input bounds.
The interpolation compactor's coefficient-norm bound, safe integer base,
integer-valued binomial formula, and denominator-clearing extension are valid.
The cases D=0 and L=1 are handled. The monomial-curve specialization requires
a nonzero pullback; a nonzero multivariate polynomial alone is insufficient.
The larger base is justified by its bounded coefficients.

The retained Appendix A prerequisite was checked because it underlies the
conditional reductions: the pullback coefficient count with N=n³,
r=floor(n²/4), D=2¹⁶N gives a nonzero height-one annihilator. Its n=2 endpoint
and the n≥3 numerical inequalities are valid. This existential counting
argument supplies neither an efficient representation nor a detecting list.
Corollary 2.3 and Corollary 4.2 keep these missing premises explicit.

Theorem 5.3 uses [Efremenko–Garg–Oliveira–Wigderson, Theorem 3](https://www.math.ias.edu/~avi/PUBLICATIONS/EfremenkoGaOlWi2018.pdf)
separately in the k independent arguments, giving (8n)^kρ. The pure-tuple rank
cost is ρ; the graph has maximum degree at most 3(n−1). Greedy coloring then
prevents strict detection at q≥8n+Δ, so the largest lower bound certifiable
by this threshold is at most 11n−3, with the stated integer endpoint.
The applicable threshold is exactly [Doležálek–Michałek, Corollary 3.5](https://arxiv.org/html/2602.12762v1),
whose looseness is discussed in that source. This is not a tensor border-rank
upper bound or a limitation on all nonlinear methods. The separate exterior
binomial-ratio proof and dimension ceiling are also valid for the allowed
block and shift endpoints, including n=1.

The ordinary Koszul pure-tensor rank bound and closure argument correctly
turn nonzero modular minors of the integer candidate into complex border-rank
lower bounds. The finite values for n=2,…,9 are 2,4,5,8,9,12,12,15. They do
not establish an all-dimension quadratic lower bound. Prior exponential-time
constructions and other nested-archive claims are excluded from this PASS.

One nonblocking reference typo occurs in the supplied review: its controlled-list
corollary is called “2.2”; the actual report numbers it **2.3** (Remark 2.2
intervenes). The theorem statement, proof, and canonical scope are unaffected.

## Fresh computation and visual evidence

- AC-05 full submitted replay: 36 groups, 163 determinant evaluations and 13
  grouped-action cases, including third powers, all passed. The four deliberate
  corruptions and scalar-intersection negative control passed. Normal and
  optimized Python runs both retain the checks.
- AC-06 submitted suite: all 40 tests passed normally and under `-O`, including
  rational input, coefficient/degree endpoints, graph counts, exterior bounds,
  minor checks and the second-prime small-dimension cross-check.
- `independent_checks.py` imports no submitted module. It reconstructs all
  twelve AC-05 local minors symbolically with SymPy, checks the local kernels
  and exceptional ranks, and derives the exact rational commutators directly
  from the tensor supports. These checks prove the local polynomial identities
  symbolically rather than by selected parameter values.
- The same fresh script builds each signed AC-06 Koszul matrix independently
  from row/column exterior subsets and the displayed exponent formula. It
  verifies every selected minor modulo 65521, including the 1050×1050 minor
  for n=9. Duplicate-row corruption is rejected for every dimension. Independent
  CRT/interpolation implementations preserve all 702 detected degree-two
  height-one example polynomials; the unsafe base-two curve control and all
  exterior blocks through n=59 also pass. Both normal and optimized runs pass.
- Visually inspected all **35** canonical/publication pages: one canonical
  page per problem, the 19-page AC-05 submission and 14-page AC-06 submission.
  No clipping, overlapping tables, lost equations or unreadable labels were
  found. The 18 and 13 original report pages respectively raster-match the
  publication pages after each cover exactly; `pdf-qa.json` records this.

The finite checks support algebraic premises and examples. The direct written
arguments above supply the unbounded quantifiers and field/closure reasoning.

## Reproduction

Use a scratch copy of `references/holden-ac-2026-09-14/submitted/`, called
`$SUBMITTED` below. Python with NumPy and SymPy is needed for AC-06 and the fresh
checker. AC-05's submitted replay requires only the standard library.

```sh
python3 "$SUBMITTED/AC05_power_rigidity/code/replay_certificates.py" --output /tmp/ac05-replay.json
python3 "$SUBMITTED/AC06_round4/verify.py" --no-write
python3 independent_checks.py "$SUBMITTED"
python3 -O independent_checks.py "$SUBMITTED"
```

The actual scientific runtime was `/private/tmp/nla-batch-python/bin/python`.
Recorded command/runtime details are in `reproduction.json`; input hashes bind
the review to the precise submitted files. `SHA256SUMS` covers this compact
evidence bundle. Scratch package copies and rendered page images are deliberately
not part of the commit-ready bundle.
