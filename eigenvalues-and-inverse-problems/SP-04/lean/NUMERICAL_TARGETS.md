# SP-04 — complete pre-proof target dossier

Prepared 2026-09-15. This is source review and exact-arithmetic preparation,
**not Lean verification or an independent final referee approval**. No Lean
proofs or canonical files were changed. Two independent exact-statement reviews
must approve the eventual boundary before implementation.

## 1. Identity, selection and attribution

- Permanent ID: **SP-04**.
- Canonical path: `eigenvalues-and-inverse-problems/SP-04/README.md`.
- Complete original proof: `solution.md` and `solution.tex` beside that README.
- Separate worktree: `/private/tmp/nla-formalization-sp04-20260915`, published
  base `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`.
- Original mathematical proof: **Matthew J. Colbrook, Department of Applied
  Mathematics and Theoretical Physics, University of Cambridge**.
- Requested formalization credit: **George Stepaniants, Department of Computing
  and Mathematical Sciences, California Institute of Technology**. Add no contact
  email and preserve the historical source files and their original attribution.
- The original question and stationary/elimination framework remain credited to
  Jasmijn A. Baaijens and Jan Draisma.

The full canonical statement, all four source proof sections and the historical
independent review were read. The argument is sound for its stated full scope.
The candidate is tractable because the scalar inequalities are elementary and
exact, and the full-dimensional genericity step can use three-dimensional
characteristic polynomials rather than a general continuity theorem for singular
values. The remaining targets have not been removed or weakened; this is an
ordering decision within the campaign.

The [published original paper](https://pure.tue.nl/ws/files/3846347/391917266748824.pdf)
defines “general” by exclusion of a proper Zariski-closed set (published p.175)
and poses the minimum-absolute-root selection question in Problem 4.3 (p.186).
The canonical entry's actual stationary-pair formulation is the target; proving
an independently defined elimination algorithm correct is unnecessary.

Immutable complete-file source hashes are in `reviews/initial/source-hashes.json`
and the diagnostic output `independent-exact-check.json`.
The historical source review additionally records the distinct normalized
mathematical-block hash
`77b6c6240eab1eab1cd7f9326a95a4bb7455188f951c11718c1b8c07cf691d95`.
Do not conflate that block hash with a current whole-file hash.

## 2. Complete original mathematical target

For each integer n≥2, define

```
G_n = {X ∈ ℝ^(n×n) : det X ∈ {-1,1}},
‖Y‖_F = sqrt(Σ_i Σ_j Y_ij²),
C(U) = {(X,c) ∈ G_n × ℝ : Xᵀ(U-X)=c I_n}.
```

For algebraically generic real U, C(U) is finite. Choose a real stationary pair
(X*,c*) minimizing |c|. On the generic locus where this choice is unique, does
X* globally minimize ‖U-X‖_F over every X∈G_n, for every dimension n≥2?
“Generic” means outside a proper real algebraic exceptional set. Both determinant
signs are allowed. Invertibility and distinct squared singular values are part
of the regular locus. The question is about the globally nearest matrix, not
merely a local minimum or a small residual.

### 2.1 Recommended exact semantic boundary

- `stationaryPairs U` is the set of **all** pairs `(X,c)` in the full real matrix
  space times ℝ satisfying the literal `Stationary U X c` condition.
- The actual `RegularData U` is `U.det ≠ 0 ∧ (Uᵀ*U).charpoly.roots.Nodup`.
  For a general real polynomial, root-list nonduplication alone would not
  account for nonreal roots. Here the real Gram matrix is Hermitian, so its
  actual characteristic polynomial splits completely over ℝ by Mathlib's
  Hermitian spectral theorem. Thus `roots.Nodup` expresses genuinely distinct
  squared singular values. The `regular_svd` export proves this property for
  all witness data. “Regular” is not defined as membership in the counterexample
  family.
- The actual `UniqueLeastStationary U X c` asserts stationarity, |c|≤|d| for
  every stationary pair (Y,d), and equality of both X and c whenever the
  absolute multipliers tie. Uniqueness of just the numeric multiplier would
  be insufficient.
- The actual `frobeniusSq X` is `Σ_i Σ_j (X i j)^2`, and
  `frobeniusNorm X` is its nonnegative `Real.sqrt`. These are the literal
  Frobenius quantities, not the default norm on a Pi type of matrix entries.
  `IsNearest U X` is `Feasible X` and the direct global inequality
  `∀ Y, Feasible Y → frobeniusNorm (U-X) ≤ frobeniusNorm (U-Y)`.
  A strictly improving feasible Y refutes it. No unproved infimum/minimum
  identification is used.
- Represent exceptional sets using actual multivariate polynomials in the n²
  real entries, with nonzero polynomial meaning algebraic nonzero. The final
  generic counterexample theorem should say, for **every nonzero polynomial P
  in the nine entries**, there is a real 3×3 U with P(U)≠0, RegularData U,
  finite `stationaryPairs U`, a unique least-absolute stationary pair, and a
  feasible matrix with strictly smaller actual Frobenius distance.
- This last theorem defeats any proper real algebraic exceptional set: such
  a set lies in the zero set of a nonzero defining polynomial. The actual
  `GenericSelectionRule n` quantifies over one arbitrary nonzero n²-variable
  polynomial and then every U outside its zero set, with `RegularData U`,
  finite `stationaryPairs U`, and a `UniqueLeastStationary` pair as premises.
  `AllGenericSelectionRules` requires this for every n≥2. The n=3 witnesses
  prove every premise, so they negate that full statement.
- No exception needed for stationary-set finiteness is hidden in a premise:
  **finiteness of the full stationary set is a mandatory witness property**.
  Section 6 supplies a short algebraic proof. The selected pair exists and is
  uniquely least independently of that finiteness proof.

All original quantifiers remain in the claim being negated. A single diagonal
matrix, or an open set only within the three-dimensional diagonal subspace,
would not refute the algebraic-generic target.

## 3. Full scalar family and exact selected pair

Take every real triple

```
7/4 < s₁ < s₂ < s₃ < 44/25,    D=diag(s₁,s₂,s₃),    T=13/25.
```

For t≥0 define actual real square-root expressions

```
a_i(t) = (s_i + sqrt(s_i²+4t))/2,
b_i(t) = (sqrt(s_i²+4t)-s_i)/2,
g(t)   = b₁(t) a₂(t) a₃(t).
```

For t>0, a_i>0, b_i>0, a_i b_i=t, and a_i and −b_i are exactly the two real
roots of x²−s_i x−t=0. The function g is continuous on [0,T] and strictly
increasing there, with g(0)=0 and g(T)>1. Hence there is a unique t*∈(0,T)
with g(t*)=1. Set

```
X* = diag(-b₁(t*), a₂(t*), a₃(t*)),    c* = -t*,
Y  = diag( b₁(t*), a₂(t*), a₃(t*)).
```

Then det X*=−1, det Y=1, and X*ᵀ(D−X*)=c*I. Moreover

```
‖D-X*‖_F² − ‖D-Y‖_F² = 4 s₁ b₁(t*) > 0.
```

Thus the conclusion must include the strict **unsquared** Frobenius comparison
as well, using positivity and the square-root semantics. The improving Y need
not be stationary; feasibility and strict improvement suffice.

The retained source example s=(1751,1755,1759)/1000 witnesses nonemptiness.
No numerical approximation of t* is needed in the proof or frozen target.

## 4. Every stationary matrix, including all real multiplier branches

### 4.1 Reduction of the full matrix equations

For an arbitrary stationary (X,c), |det X|=1 makes X invertible. Put S=XᵀX.
Direct algebra gives

```
D = X + c X⁻ᵀ,
DᵀD = S + 2c I + c² S⁻¹.
```

Thus S commutes with DᵀD=diag(s_i²). Its three diagonal entries are distinct,
so every off-diagonal entry of S vanishes. The original equation also gives
`XᵀD=S+cI`; because every s_i is nonzero, its off-diagonal entries force X
itself to be diagonal. This last step avoids needing a separate inverse of
`I+cS⁻¹`. Consequently **all** stationary pairs are exactly the scalar triples

```
x_i²−s_i x_i+c=0 for i=1,2,3,    |x₁x₂x₃|=1.
```

Conversely those equations give the full matrix stationary pair. Negative x_i
and either determinant sign must remain available.

### 4.2 Exclude 0≤c≤T with algebraic square-root estimates

At c=0, invertibility forces x_i=s_i, whose product exceeds one.
For 0<c≤T put

```
r_i(c)=(s_i+sqrt(s_i²−4c))/2.
```

The exact estimates are

```
s_i²−4c > 393/400 > (99/100)²,
1 < r_i(c) < 44/25,
r_max−r_min < 1/50,
r_max/r_min < 51/50.
```

No derivative or mean-value theorem is necessary. For s_j>s_i,

```
sqrt(s_j²−4c)−sqrt(s_i²−4c)
  = (s_j−s_i)(s_j+s_i)/(sqrt(s_j²−4c)+sqrt(s_i²−4c)).
```

The factor after `(s_j−s_i)` is less than `(88/25)/(99/50)=16/9`.
Thus `r_j−r_i < (25/18)(s_j−s_i) < 1/72 < 1/50`.
Both quadratic roots are positive and equal to r_i or c/r_i. The all-large
selection has product >1. Every other selection has product at most the
largest selection containing exactly one small root, which is bounded by

```
c r_max²/r_min < (13/25)(44/25)(51/50)
              = 14586/15625 < 1.
```

This accounts for all eight patterns. Positive multipliers above T cannot
compete with |c*|<T, regardless of whether roots collide or exist there.
A suitable small LeanCert kernel certificate is `14586/15625 < (1:ℝ)`, genuinely
consumed in this exclusion argument. Quantified square-root inequalities need
ordinary kernel proofs; no interval subdivision is required.

### 4.3 Existence and unique least absolute multiplier

At t=T, the polynomial a²−s_i a−T at a=2 is less than
`4−2(7/4)−13/25 = −1/50`, so a_i(T)>2. Also

```
(1/4)²+s₁/4 < 1/16+11/25 = 201/400 < 13/25,
```

so b₁(T)>1/4 and g(T)>1. Monotonicity follows from the actual square-root
formulas; a_i and b_i are strictly increasing for t≥0. The intermediate value
theorem supplies the unique t* above.

For a negative multiplier c=−t, all-positive roots have product >1. Every
nonempty negative-index pattern E has absolute product

```
(a₁a₂a₃) ∏_{i∈E} q_i,    q_i=t/a_i².
```

For t>0, `0<q₃<q₂<q₁<1`. Hence the unique largest pattern at fixed t is
E={1}, whose product is g(t). For 0<t<t*, all products are <1. At t=t*, only
E={1} has product one. This proves the unique least pair among all negative
multipliers, and §4.2 proves uniqueness among every real stationary pair.
There is **no need** to show that each other negative pattern eventually reaches
one or to prove asymptotics as t→∞. Those additional source observations are
not needed for this target.

## 5. Full nine-dimensional open set without singular-value continuity

Define six positive rational spectral endpoints

```
α₁=(1750/1000)², β₁=(1752/1000)²,
α₂=(1754/1000)², β₂=(1756/1000)²,
α₃=(1758/1000)², β₃=(1760/1000)².
```

For a real 3×3 U the actual `gramPolynomialValue U t` is
`h_U(t)=det(tI−UᵀU)`. The actual `counterexampleFamily` O is defined by
**three pairs of opposite strict signs**, without prescribing their orientation:

```
∀ i=1,2,3, h_U(α_i) * h_U(β_i) < 0.
```

This product-negative condition is exactly what the intermediate value theorem
needs. It is a definition only in terms of the entries and three strict
polynomial inequalities; it contains no spectral, SVD, finiteness or failure
conclusion as an assumption. Each determinant and product is continuous in all
nine real entries, so O is open in the **full** matrix space.

At the original rational diagonal example D₀=diag(1751,1755,1759)/1000, the six
values have signs `(−,+,+,−,−,+)`, which satisfy all three product conditions.
Their exact values, with common denominator10¹⁸, have numerators

```
−1937653044525,   905786883351,
  648098176275,  −649206984825,
 −910443880269,  1954285183575.
```

The independent checker verifies all six exactly. Thus O is nonempty. By the
intermediate value theorem each of the three disjoint intervals contains a
root of the actual monic degree-three Gram characteristic polynomial. These
three distinct roots exhaust its roots, each has multiplicity one, and all
are positive. They are the squared singular values. Their positive square
roots lie in the scalar box of §3; the endpoints at 7/4 and 44/25 cause no
problem because the root intervals are open.

Mathlib's real Hermitian spectral theorem gives an orthogonal Q diagonalizing
UᵀU with those roots, ordered increasingly by a finite permutation. With
s_i their positive square roots, set `P=U Q diag(1/s_i)`. Direct multiplication
proves PᵀP=I, P is square orthogonal, and `U=P D Qᵀ`. This establishes the
needed SVD locally without assuming or implementing a general SVD-continuity
theorem. It proves actual invertibility and simple Gram spectrum for every
U∈O, not just for D₀.

For every pair of real orthogonal P,Q, the map `X↦PᵀXQ` is a bijection
between the full stationary sets for U and D. It preserves the actual scalar
multiplier, absolute determinant, and Frobenius distance. This transfers the
unique least pair, strict feasible improvement, and full finiteness theorem
to every U∈O. Orthogonal matrices of both determinant signs are allowed.

## 6. Mandatory finiteness of the full stationary set

This supplement makes finiteness explicit instead of invoking an unformalized
generic-finiteness theorem from the literature. Fix any scalar-box triple s.
Over the polynomial ring ℝ[c], define

```
T_i(c) = [[s_i,-c],[1,0]],
K(c)   = T₁(c) ⊗ T₂(c) ⊗ T₃(c),
R(c)   = det(K(c)−I₈) det(K(c)+I₈).
```

For any stationary scalar triple, `T_i(c)(x_i,1)ᵀ=x_i(x_i,1)ᵀ`.
The tensor vector `v=(x₁,1)⊗(x₂,1)⊗(x₃,1)` has last coordinate1 and obeys
`K(c)v=(x₁x₂x₃)v`. Its eigenvalue is ±1, so R(c)=0. This implication uses
actual determinant singularity, not an assumed resultant specification.

At c=0 each T_i and K are lower triangular. K has only one nonzero diagonal
entry `s₁s₂s₃`. Therefore

```
R(0)=(1−s₁s₂s₃)(1+s₁s₂s₃)=1−(s₁s₂s₃)²≠0.
```

Thus R is a nonzero univariate polynomial, with finitely many real roots. For
each multiplier, each x_i lies among the finitely many roots of the monic
quadratic `X²−s_i X+c`, so the possible triples form a finite product. The
all-stationary diagonal reduction makes the entire matrix/multiplier set finite.
No explicit coefficient expansion of the 8×8 determinants, no degree bound
for R, and no enumeration of positive stationary roots are necessary.
This proof transports to every U∈O by §5.

## 7. The algebraic-generic qualifier

For every nonzero `P : MvPolynomial (Fin 3 × Fin 3) ℝ`, prove that P does not
vanish throughout O. There are two small routes using established polynomial
facts; either must apply in all nine coordinates.

1. A nonempty finite-product open set contains a box of open real intervals.
   Every side is infinite. `MvPolynomial.funext_set` says that polynomials
   equal on a box with infinite sides are equal. Applied to P and zero, it
   rules out vanishing throughout O.
2. Choose x∈O and any y. Substitute the affine line `x+t(y−x)` into P to get
   a genuine univariate polynomial q. If P vanishes on O, continuity gives
   an interval about0 where q vanishes. A nonzero univariate polynomial has
   only finitely many roots, so q=0, and q(1)=P(y)=0. Since y was arbitrary,
   `MvPolynomial.funext` implies P=0, a contradiction.

This supplies U∈O outside each proposed polynomial exception. The regularity,
finite stationary set, uniquely selected pair and strict improvement are all
proved properties of U. The full generic rule is therefore false; no unproved
“generic” hypothesis is supplied as an axiom or an exclusion in the definition.

## 8. Exact numerical diagnostics and what they do not prove

In the packaged Lean project, run `python3 reviews/initial/independent-exact-check.py`.
In the external preparation directory, run `python3 independent-exact-check.py /path/to/source-repository`.
The checker is fresh standard-library rational arithmetic. It verifies the six strict signs, all
rational constants in §4, and the finiteness eliminant mechanism at exact data.
Its output is `independent-exact-check.json`, including all source hashes.

An **optional diagnostic only**, outside the proposed frozen target, gives a
fully rational stationary point inside the same source family:

```
t=199/400,
x=(-1000000/4020021, 2003/1000, 2007/1000),
s_i=x_i−t/x_i,
s=(2815953199247759/1608008400000000,
   3514509/2003000, 3530549/2007000).
```

Its x product is −1, its multiplier is −199/400, its s entries satisfy the
strict ordered source box, and changing x₁ to |x₁| strictly improves squared
distance. The checker also verifies the nonzero tensor eigenvector, R(c)=0,
and R(0)≠0 at that exact sample. This is not an additional target obligation
and does not replace the original rational D₀ used to witness O's nonemptiness.

The checker does **not** prove uniqueness of selection, all-real branch
classification, stationary-set finiteness, full-dimensional openness or
algebraic genericity. Those require the complete Lean proofs above.

## 9. Pinned Mathlib API plan and computation budget

Pinned versions are the established campaign Lean4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The following were located in their
actual sources; this is API reconnaissance, not compiled proof code.

- `Mathlib/Analysis/Matrix/Spectrum.lean`:
  `Matrix.IsHermitian.eigenvectorUnitary`, `.spectral_theorem`, `.charpoly_eq`,
  `.roots_charpoly_eq_eigenvalues`, `.eigenvalues₀_antitone`, and
  `.spectrum_real_eq_range_eigenvalues`. These are sufficient for the local
  Gram diagonalization and finite reordering. No ready matrix SVD theorem or
  singular-value continuity theorem was found.
- `Mathlib/Analysis/Matrix/PosDef.lean`:
  `.posDef_iff_eigenvalues_pos` and `.eigenvalues_pos` if positivity is encoded
  through eigenvalues. Direct Gram orthogonality algebra also suffices.
- `Mathlib/Analysis/InnerProductSpace/SingularValues.lean` has actual
  `LinearMap.singularValues`, `singularValues_fin` and
  `sq_singularValues_fin`. Use these if a public singular-value bridge is
  requested; do not substitute matrix entry norms for singular values.
- `Mathlib/Topology/Order/IntermediateValue.lean`:
  `intermediate_value_Icc`, `intermediate_value_Ioo` and their reversed-order
  versions, for both g(t*)=1 and the three Gram characteristic roots.
- `Mathlib/Algebra/MvPolynomial/Funext.lean`:
  `MvPolynomial.funext_set`, `funext_set_iff`, `funext`, `funext_iff`.
  The infinite-box version is particularly direct for the genericity step.
- Polynomial root finiteness, actual characteristic polynomial evaluation,
  degree3 and root multiplicities are existing polynomial/matrix APIs.
  `RingHom.map_det` commutes evaluation with the companion-matrix determinants.
- `Matrix.IsHermitian.apply`, actual matrix inverse/unit laws, determinant
  multiplicativity, transpose multiplication and trace/Frobenius sum identities
  support the all-stationary reduction and orthogonal transport.
- `Continuous.matrix_det`, finite coordinate continuity and `fun_prop` suffice
  for the open set; there is no need for a perturbation bound on ordered
  eigenvalues or an inverse-function theorem.
- `Real.sqrt` continuity, squared-root identities and strict monotonicity,
  together with `ring`, `nlinarith`, and positive-denominator inequalities
  establish the scalar parts without differentiating the roots.
- LeanCert explicit kernel mode certifies a genuinely consumed closed rational
  comparison such as `14586/15625<1`. Rational finite matrix checks may use
  `norm_num` or the kernel-producing `eval_det` tactic already used for PF-02.

The only finite branch enumeration is the eight patterns arising from three
quadratics; the entries and multipliers remain arbitrary real numbers. Avoid
expanding the full companion eliminant: only its vanishing implication and
one nonzero evaluation are needed. No numerical root search for t*, sampled
matrix family, spectral-norm interval approximation, or large determinant
coefficient table is required.

## 10. Exact typed export boundary and review gates

I inspected the actual `NLA/SP04/Definitions.lean`, `Challenge.lean` and
`comparator.json` in the new SP-04 project. The table below aligns with all
**eleven** typed Challenge exports. The specification module contains eleven
intentional placeholders and no proof implementation; names below are no
longer provisional. Comparator lists all eleven and has no replaceable
definition holes.

| Exact export | Required content of the actual signature |
|---|---|
| `numerical_bounds` | The four exact inequalities `(99/100)^2 < 49/16−52/25`, `275/198 < 2`, `(13/25)(44/25)(51/50)<1`, and `201/400<13/25`. |
| `diagonal_stationary_iff` | For every admissible real triple s, every real matrix X and every real c, the full stationary condition is equivalent to a diagonal scalar triple satisfying all three quadratics and absolute product one. |
| `diagonal_counterexample` | For every admissible s, some 0<t<13/25 gives `UniqueLeastStationary` at the actual `selectedMatrix s t` and multiplier −t, together with the actual `improvedMatrix s t` feasible and strictly closer in the unsquared `frobeniusNorm`. |
| `diagonal_finite` | The entire `stationaryPairs (Matrix.diagonal s)` set is finite for every admissible s, not merely the selected branch or a bounded range of multipliers. |
| `orthogonal_transport` | In every dimension, for every pair P,Q satisfying both actual orthogonality equations, determinant feasibility and stationarity are equivalent under two-sided transport; the actual Frobenius norm is preserved. |
| `spectral_family` | `counterexampleFamily` is open in the full matrix topology, contains the unchanged `sampleMatrix`, and every member has a genuine `HasSVD U s` with `Admissible s`. No eigenvalue continuity is assumed. |
| `regular_svd` | Every actual `HasSVD U s` with admissible s yields `RegularData U`, including actual Gram-characteristic `roots.Nodup`. |
| `open_family_counterexamples` | Every U in that full open family satisfies `SelectionFails U`: invertibility, simple Gram spectrum, full stationary-set finiteness, unique least pair, and a strictly improving feasible matrix. |
| `algebraic_avoidance` | For every nonempty open set of real 3×3 matrices and every nonzero polynomial in all nine entries, some matrix in that open set has nonzero polynomial evaluation. |
| `generic_counterexamples` | Every nonzero nine-variable polynomial leaves a `SelectionFails` witness outside its zero set. |
| `canonical_counterexample` | `¬ AllGenericSelectionRules`, negating the original rule across all n≥2 and every permitted proper algebraic exception. |

The scalar and generic counterexample definitions contain no hidden finiteness
or diagonal-only scope restriction: finiteness is explicitly proved, and the
stationary comparison quantifies over the full real matrix/multiplier set.
`HasSVD` means an actual factorization `U=P*diagonal(s)*Qᵀ` with both P,Q
orthogonal; it is not an abstract assertion that undefined singular values
exist. Real Gram spectral theory supplies its bridge to the source's singular
values.

The optional rational stationary sample is diagnostic, not a substitute or an
extra canonical theorem. The original sample and source proof are preserved in
full. Final metadata must distinguish pre-proof statement approval, local proof
compilation, independent final review, Comparator correspondence, real Linux
reproducibility and permitted-axiom checks. No status promotion is justified by
this dossier.
