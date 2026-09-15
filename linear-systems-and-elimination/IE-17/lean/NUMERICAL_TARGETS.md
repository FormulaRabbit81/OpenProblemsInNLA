# IE-17: exact pre-proof mathematical and numerical dossier

Prepared 2026-09-15 by the independent target-review agent. This document is a
statement/proof review and an exact-arithmetic reconstruction, **not a Lean
verification**. No IE-17 Lean implementation or canonical-file edit was made.
The draft boundary was read after the numerical reconstruction and passed this
agent's correspondence review; final independent review and freezing remain
required before proof implementation. IE-15 publication and verification are a separate, unfinished
campaign step at the time of this preparation.

## 1. Identity, source, attribution, and review outcome

- Permanent ID: **IE-17**.
- Canonical page: `linear-systems-and-elimination/IE-17/README.md`.
- Reviewed checkout: `/private/tmp/nla-formalization-ie17-20260915`, base
  `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`.
- Full original solution:
  `references/colbrook-recovered-2026-09-11/manuscripts/IE-17.tex`.
- Original proof attribution: **Matthew J. Colbrook, Department of Applied
  Mathematics and Theoretical Physics, University of Cambridge**. Preserve this,
  the supplied-notes/AI-assistance disclosure, and the original manuscript.
- Requested formalization credit, distinct from the original proof attribution:
  **George Stepaniants, Department of Computing and Mathematical Sciences,
  California Institute of Technology**. No contact email.
- Current source hashes are in adjacent `IE-17-source-hashes.json`.

**Independent informal verdict: PASS for the complete canonical negative
resolution.** I read the complete solution and independently recomputed the
iterates, the feasible upper perturbation, the lower certificate, and both
approximation values with rational arithmetic. I found no material mathematical
gap in the written argument. The minimum-attainment and operator/pseudoinverse
bridges below are essential explicit formalization obligations; numerical
certificates alone do not discharge them.

The primary [Fong thesis](https://web.stanford.edu/group/SOL/dissertations/david-fong-thesis-online.pdf)
confirms the induced matrix 2-norm convention in its notation on printed p. 14,
defines the quantities on pp. 56–57, and makes both monotonicity conjectures in
§7.2.1, p. 118. The [LSMR journal paper](https://web.stanford.edu/group/SOL/software/lsmr/LSMR-SISC-2011.pdf)
has a different default convention for matrix norms in §1.2; its general
Frobenius convention must not be used to silently change this spectral target.

## 2. Complete canonical mathematical statement

The original mathematical target, preserved here without narrowing its domain:

> Let A ∈ ℝ^(m×n) and b ∈ ℝ^m. In exact arithmetic, start LSMR at x₀ = 0:
> equivalently, xₖ minimizes ‖Aᵀ(b − Ax)‖₂ over
> Kₖ(AᵀA, Aᵀb). Work up to its exact termination and use its minimum-length
> iterate if necessary. Let r = b − Ax and define the matrix-only normwise
> backward error
>
> μ(x) = min {‖E‖₂ : (A + E)ᵀ((A + E)x − b) = 0}.
>
> For x ≠ 0, put Kₓ = [Aᵀ, (‖r‖₂/‖x‖₂)I]ᵀ,
> vₓ = [rᵀ, 0ᵀ]ᵀ, and
>
> μ̃(x) = ‖Kₓ Kₓ† vₓ‖₂ / ‖x‖₂.
>
> Here † is the Moore–Penrose inverse; at an exact least-squares solution set
> both errors to zero. Are both sequences μ(xₖ) and μ̃(xₖ) nonincreasing,
> for successive nonzero LSMR iterates? These two closely related claims are
> counted together, as in the source. The right-hand side b is kept fixed in
> the backward-error model.

The answer is **no to each claim**, established by the same pair of successive
iterates. The full exported resolution must express both refutations, for
example `¬ ExactErrorMonotone ∧ ¬ ApproxErrorMonotone`. Merely proving
`¬ (ExactErrorMonotone ∧ ApproxErrorMonotone)` would be logically weaker than
the supplied complete resolution.

### 2.1 Exact LSMR and termination semantics

Write H = AᵀA and g = Aᵀb. Define
K₀(H,g) = {0} and Kₖ(H,g) = span{Hʲg : 0 ≤ j < k}. An exact iterate xₖ
belongs to this subspace and minimizes the genuine Euclidean norm of g − Hx
there; among minimizers it has minimum Euclidean length. Squared-norm
minimization may be used internally after proving its equivalence.

A complete finite exact run includes x₀ = 0, its final iterate x_ℓ, these
minimization properties for every k ≤ ℓ, and first exact termination at ℓ:
Aᵀ(b − Ax_ℓ) = 0 and this normal residual is nonzero at every k < ℓ.
Termination is **not** the condition b − Ax = 0. The concrete witness is
inconsistent and its final residual is (0,0,0,1).

The monotonicity quantifiers range over the original arbitrary real dimensions,
matrices, and right-hand sides, and genuine exact runs. They must not assume
full rank universally. The counterexample has full column rank, so every
minimizer used in it is unique and hence automatically has minimum length.
Its x₁ and x₂ are adjacent, both nonzero, and both strictly before termination;
there is consequently no ambiguity about “successive nonzero” for the witness.
For the approximation a totalization at x = 0 is harmless only if its target
domain explicitly excludes that case.

### 2.2 Actual norms and the optimization-defined error

For a real vector y, ‖y‖₂ = sqrt(Σᵢ yᵢ²). For any rectangular real matrix E,
‖E‖₂ is the induced Euclidean operator norm, equivalently the operator norm of
its continuous linear map between Euclidean spaces. It is neither the entrywise
Frobenius norm nor a norm induced by the plain function-space sup norm.

The feasible perturbation set contains **all** E ∈ ℝ^(m×n) satisfying the
displayed normal equations with b fixed. No symmetry, sparsity, rank, or
support constraint may be added. Defining μ by an infimum is acceptable only
with a theorem identifying it with the attained minimum in the canonical page.
The attainment proof is finite-dimensional: the feasible set is nonempty
(E = −A), is closed, and its intersection with the closed ball of radius ‖A‖₂
is compact; continuous norm attains a minimum there, which is global. At exact
least-squares solutions E = 0 is feasible, so this minimum equals zero.
The current draft instead uses the direct relation `IsLeast (errorSet A b x) δ`,
which includes both feasibility/attainment and the all-perturbation lower bound.
Its exported `optimal_errors` explicitly proves such attained minima exist at
both counterexample iterates. This relational encoding faithfully represents
the canonical minimum; a global total choice function is unnecessary for the
negative resolution. A general existence lemma is reusable, but existence at
the actual witness dimensions is sufficient for this target.

### 2.3 Actual Moore–Penrose semantics

Kₓ is the vertical stack of A and ηIₙ, η = ‖r‖₂/‖x‖₂, with m+n rows and n
columns. vₓ stacks r and n zero entries. The approximation must use its actual
Moore–Penrose inverse or a proved equivalent orthogonal projection. For a real
matrix K, a candidate Q must satisfy all four Penrose equations:

```
K Q K = K,     Q K Q = Q,
(K Q)ᵀ = K Q, (Q K)ᵀ = Q K.
```

Prove uniqueness or equivalence to the orthogonal projection onto range K.
For the active branch x ≠ 0 and Aᵀr ≠ 0, r ≠ 0 and η > 0; thus K has full
column rank even when A does not. Its actual pseudoinverse is
Q = (KᵀK)⁻¹Kᵀ. The exact least-squares branch is zero, as specified canonically.
One must **prove**, not substitute as a definition, the useful identity

```
μ̃(x)² = (Aᵀr)ᵀ (s AᵀA + ρ I)⁻¹ (Aᵀr),
s = ‖x‖₂², ρ = ‖r‖₂².
```

This follows from the symmetric idempotent projector KQ, from
KᵀK = AᵀA + (ρ/s)I, and from the positive denominators. The bridge is a major
part of target correspondence; rational evaluation of its right side alone
would not verify the canonical approximation.

## 3. Exact witness and complete trajectory

Use exactly

```
A = [[1,0,0], [0,6,0], [0,0,5], [0,0,0]],
b = (11,1,1,1),
H = diag(1,36,25), g = (11,6,5), C = AAᵀ = diag(1,36,25,0).

x₀ = (0,0,0),
x₁ = (1021/31201)g = (11231,6126,5105)/31201,
x₂ = (16321g − 383Hg)/110438 = (87659,7599,16865)/55219,
x₃ = (11,1/6,1/5).

r₁ = (331980,−5555,5676,31201)/31201,
r₂ = (519750,9625,−29106,55219)/55219,
r₃ = (0,0,0,1).

Aᵀr₁ = (331980,−33330,28380)/31201,
Aᵀr₂ = (519750,57750,−145530)/55219,
Aᵀr₃ = (0,0,0).
```

The normal residual norms obey
‖Aᵀr₁‖₂² = 3593700/31201 > 5336100/55219 = ‖Aᵀr₂‖₂² > 0.
Thus this example respects ordinary normal-residual monotonicity.

Let Vₖ have columns g,Hg,…,H^(k−1)g. To prove each xₖ is the unique Krylov
minimizer, verify membership, `(H Vₖ)ᵀ(g − Hxₖ) = 0`, and injectivity of H Vₖ.
Expanding the quadratic objective around xₖ then proves its global minimizing
property. Full-column rank A and independent Vₖ columns also prove uniqueness.
The following are exact rational certificates, independently recomputed:

| k | coefficients in Vₖ | Gram matrix (H Vₖ)ᵀ(H Vₖ) | determinant |
|---|---|---|---|
| 1 | (1021/31201) | [62402] | 62402 |
| 2 | (16321/110438, −383/110438) | [[62402,2070362],[2070362,70231922]] | 96213585600 |
| 3 | (961/900, −31/450, 1/900) | [[62402,2070362,70231922],[2070362,70231922,2420923082],[70231922,2420923082,84467679842]] | 7531072718400000000 |

Also det V₃ = −3049200 ≠ 0. This proves K₃ = ℝ³ and exact termination at 3;
the explicit earlier normal residuals prove that termination was not earlier.

| Quantity | k = 1 | k = 2 | k = 3 |
|---|---|---|---|
| sₖ = ‖xₖ‖₂² | 189724262/973502401 | 8026273307/3049137961 | 108961/900 |
| ρₖ = ‖rₖ‖₂² | 111247297802/973502401 | 274129000322/3049137961 | 1 |

Every displayed x₁,x₂,x₃ is nonzero. No rounded iterate or floating-point
LSMR implementation is part of the certificate.

## 4. Matrix-only spectral backward error: all-perturbation lower bound

For any nonzero x, put z = Ax, s = ‖x‖₂², ρ = ‖r‖₂², and

```
D = (ρ I − r rᵀ + z zᵀ)/s.
```

The original source proves μ(x)² ≥ λ_min(tC+(1−t)D), for m > n and 0 ≤ t ≤ 1.
For formalization, a quadratic-form lower certificate replaces computation or
even definition of λ_min. This preserves the full error target.

For **arbitrary feasible E**, write B = A+E and q = b−Bx.

1. If q ≠ 0, set u = q/‖q‖₂. Then ‖u‖₂ = 1, Bᵀu = 0,
   q = u(uᵀb), Eᵀu = −Aᵀu, and Ex = r−u(uᵀb). Consequently
   `‖E‖₂² ≥ uᵀCu` and `‖E‖₂² ≥ uᵀDu`.
   The second identity uses
   `‖r−u(uᵀb)‖₂² = ρ−(uᵀr)²+(uᵀz)²`.
   A convex combination yields the lower quadratic-form bound for this E.
2. If q = 0, Ex = r gives `‖E‖₂² ≥ ρ/s` directly. This branch cannot be
   discarded: feasible perturbations can turn the problem into a consistent
   one. The original general lemma handles it using a vector in ker Aᵀ.
   For this witness the explicit rational ratio below is simpler and sufficient.

At x₂, t = 5/6, and c = 99/100, the source gives

```
(5/6) C + (1/6) D₂ − (99/100) I₄ = K/dK,
dK = 2407881992100,

K = [[206417059721, −50293465200, 1125984433750, −1435003762500],
     [−50293465200, 83658415217471, 206242965000, −26574143750],
     [1125984433750, 206242965000, 61800032332121, 80360210700],
     [−1435003762500, −26574143750, 80360210700, 11170189945871]].
```

The independently reproduced source leading principal determinants of K are

```
206417059721,
17265994657467102998545591,
960941324740480331793743845178086291011,
65442104145157248520714038046591467785805073713081.
```

### 4.1 New cheaper, stronger lower certificate — review before freezing

The following auxiliary certificate is newly derived in this review; do not
attribute these specific weights to the original manuscript. It proves a
stronger bound, without changing the original target or conclusion.

Set c* = 9901/10000, K* = K − (dK/10000)I, and v = (10000,10,185,1287).
The exact weighted diagonal-dominance margins
`K*ᵢᵢ vᵢ − Σ_{j≠i}|K*ᵢⱼ| vⱼ` are

```
(6102817984650,
 2612912207614679/10,
 1352621546092623/20,
 1055456050659373/100).
```

They are all positive. Hence diag(v) K* diag(v) is symmetric strictly
diagonally dominant with positive diagonal, and K* is positive definite.
This can be proved by a finite sum-of-squares identity, with no eigenvalue,
Sylvester-criterion, or interval computation. It establishes the uniform bound

```
uᵀ((5/6)C+(1/6)D₂)u ≥ (9901/10000) ‖u‖₂².
```

The zero-new-residual branch satisfies
`ρ₂/s₂ = 274129000322/8026273307 > 9901/10000`.
Therefore **every feasible perturbation E** at x₂ obeys
`‖E‖₂² ≥ 9901/10000`, and in particular

```
μ(x₂)² ≥ 9901/10000 > 99/100.
```

This explicit uniform margin also prevents a strict-infimum mistake. The
statement “every feasible E has norm² > c” alone does not imply that the
infimum's square is > c unless attainment or a uniform gap is proved. Canonical
minimum attainment is still required even with this stronger certificate.

## 5. Explicit feasible upper perturbation at x₁

Let κ = 1979/2000. The original construction uses w = (250,−1,1,27),
ω = wᵀw = 63231, h = wᵀAx₁ = 2796519/31201, and

```
c₀ = r₁ − w(wᵀr₁)/ω,
a₀ = −Aᵀw + (h/s₁)x₁,
E = −w wᵀ A/ω + c₀ x₁ᵀ/s₁ + h c₀ a₀ᵀ/(ω s₁ κ − h²).
```

Its denominator `ω s₁ κ − h² = 4049973517650519/973502401000` is positive.
The source's direction checks are

```
wᵀCw/ω  = 62561/63231 < κ,
wᵀD₁w/ω = 1642993919237/1713779258646 < κ.
```

The complete rational perturbation is E = B_E/dE, where

```
dE = 167211149523055806,
B_E =
 [[−165210014935131560, 11610848662197240, 2530244735132700],
  [39351326577989, −69867125644099962, −53313444486018375],
  [−21561235850426, 71865739948107360, 54839250040764540],
  [−18526767941430855, −75599190148266018, −58398875034268035]].
```

Exact arithmetic confirms `(A+E)ᵀ((A+E)x₁−b) = 0`. Proving this identity and
the positive-semidefinite Gram bound below suffices; a general spectral-norm
matrix-completion lemma is unnecessary for the counterexample.

### 5.1 New simpler upper PSD certificate — review before freezing

Let G = κI₃−EᵀE, and use the simple unimodular change of coordinates

```
T = [[1,−18,23], [0,1,0], [0,0,1]],  det T = 1.
```

Then `Tᵀ G T = M/dM`, where

```
dM = 31584381671763314443807585554000,
M =
 [[32082903136661873741517122683,
   12090505500201922856789273706,
   −8382094473667110912199943291],
  [12090505500201922856789273706,
   2465624315241079991428765050975,
   31049384466533821447752395238],
  [−8382094473667110912199943291,
   31049384466533821447752395238,
   3427462740377387654443006689990]].
```

Its diagonal-dominance margins are the positive integers

```
11610303162792839972527905686,
2422484425274344247124223382031,
3388031261437186722083054351461.
```

Thus M, TᵀGT, and G are positive definite. The same elementary symmetric
diagonal-dominance lemma can handle both upper and lower certificates. For a
symmetric matrix S, the identity

```
yᵀSy = Σᵢ (Sᵢᵢ−Σ_{j≠i}|Sᵢⱼ|) yᵢ²
       + Σ_{i<j}|Sᵢⱼ| (yᵢ + sign(Sᵢⱼ)yⱼ)²
```

proves the required positivity; zero off-diagonal terms may use either sign.
Since T is invertible, this proves `‖Ey‖₂² ≤ κ‖y‖₂²` for every y. The actual
Euclidean operator-norm bridge gives `‖E‖₂² ≤ κ`, so minimum feasibility gives
`μ(x₁)² ≤ κ`.

For cross-checking, the original leading principal minors of G are

```
32082903136661873741517122683/31584381671763314443807585554000,
4999825963008588746348642081657/63168763343526628887615171108000000,
2511823903624540305487853/292667286279497105016000000000.
```

The adjacent JSON also records an exact LDLᵀ decomposition, but the simple
congruence/diagonal-dominance certificate avoids its complicated coefficients.
The new T and margins are independently derived auxiliary arithmetic, and
should be reviewed as such before proof implementation.

The complete exact-error conclusion is therefore

```
μ(x₁)² ≤ 1979/2000 < 99/100 < μ(x₂)²,
and hence μ(x₁) < μ(x₂).
```

The unsquared inequality requires and follows from the nonnegativity of the
actual norm minima; it must appear in the final monotonicity refutation.

## 6. Exact approximation increase

After proving the Moore–Penrose/projector identity in §2.3, evaluation uses
only a diagonal inverse. With nₖ = Aᵀrₖ,

```
μ̃(xₖ)² = nₖ,1²/(sₖ+ρₖ)
         + nₖ,2²/(36sₖ+ρₖ)
         + nₖ,3²/(25sₖ+ρₖ).
```

Every denominator is strictly positive. Exact evaluation gives

```
μ̃(x₁)² =
69694107852573439503892031925 /
69323394392991282508138323472
< 503/500,

503/500 < 1007/1000,

1007/1000 < μ̃(x₂)² =
5430772101137459612205263871781350 /
5387955615790281743396033884265233.
```

The nonnegative square roots therefore strictly increase as well. This is a
second fully established refutation, not an inference from the μ increase.

## 7. Reusable Lean/Mathlib API findings

These are implementation references, not imported mathematical assumptions.
Inspect exact pinned declarations before using them. The existing IE-15
Mathlib pin at review time is `0df444a360eaa60ab8c11dca51a86af692955474`,
with Lean 4.33.1; preserve reproducibility in the eventual IE-17 project.

### Existing problem structures

- **IE-23** `NLA/IE23/Definitions.lean` uses `EuclideanSpace`/`WithLp.toLp 2`
  for the Euclidean vector norm and defines induced norms from actual norm
  ratios. `Norms.lean` proves ratio-set boundedness and nonemptiness,
  `ratio_le_inducedNorm`, `mulVec_le_inducedNorm`, and `inducedNorm_le_of_bound`.
  Those are useful proof patterns. Its Moore–Penrose formula is for **full row
  rank**: `Aᴴ*(A*Aᴴ)⁻¹`. IE-17's stacked K is full **column** rank, so its
  formula has the other orientation `(KᵀK)⁻¹Kᵀ`.
- **IE-19** supplies finite matrix/inverse certificate patterns. Its row-sum
  norm does not represent IE-17's spectral norm.
- **IE-18** uses a genuine sum of squared coordinates, its square-root
  Euclidean norm, and algebraic residual identities. Its norm/square bridges
  and finite rational matrix calculation patterns are reusable.

### Pinned Mathlib APIs

- `Mathlib/Analysis/CStarAlgebra/Matrix.lean`, scoped
  `Matrix.Norms.L2Operator`, provides the actual rectangular Euclidean operator
  norm. Relevant declarations: `Matrix.l2_opNorm_def`,
  `Matrix.l2_opNorm_conjTranspose`,
  `Matrix.l2_opNorm_conjTranspose_mul_self`, `Matrix.l2_opNorm_mulVec`, and
  `Matrix.l2_opNorm_mul`. The definition passes through `Matrix.toEuclideanLin`
  and `LinearMap.toContinuousLinearMap`. `Matrix.toEuclideanCLM` is convenient
  for square matrices; the rectangular map uses the former composition.
  The source warns that a simple matrix type ascription can select a different
  norm instance. Keep the intended Euclidean operator norm explicit.
- `Matrix.Norms.Operator` is the ℓ∞ operator norm, not the required scope.
  Ordinary function vectors also inherit a sup norm unless converted to
  EuclideanSpace. This is a high-priority statement audit check.
- No general Moore–Penrose inverse implementation was located in the pinned
  Mathlib. Define the Penrose relation and prove the full-column formula or an
  equivalent orthogonal projection characterization. Do not mistake Mathlib's
  nonsingular inverse for a general pseudoinverse.
- `Mathlib/LinearAlgebra/Matrix/PosDef.lean` has
  `Matrix.posDef_iff_dotProduct_mulVec`,
  `Matrix.PosDef.dotProduct_mulVec_pos`,
  `Matrix.PosDef.of_dotProduct_mulVec_pos`,
  `Matrix.PosDef.conjTranspose_mul_mul_same`, and
  `Matrix.PosDef.conjTranspose_mul_self`. No ready leading-principal Sylvester
  theorem was located. The finite sum-of-squares certificates above avoid it.
- `Mathlib/Topology/Order/Compact.lean` has `IsCompact.exists_isMinOn` and
  `ContinuousOn.exists_isMinOn'` for the attained minimum.
- Inner-product projection files `Projection/Minimal.lean`, `Basic.lean`, and
  `Submodule.lean` provide minimum-distance/projection existence patterns if
  generic Krylov minimizer existence is needed.

## 8. Complete-target theorem and review plan

I read the exact draft `NLA/IE17/Definitions.lean`, root `Challenge.lean`, and
`comparator.json` in the new IE-17 project. The following are the **actual eight
draft exports**, all in namespace `NLA.IE17`, not implementation theorem names
invented by this dossier. The Challenge's eight `sorry` placeholders are
explicitly specification-only and prove nothing. Freeze the independently
reviewed boundary before implementing any of them.

| Export | Complete-target correspondence |
|---|---|
| `spectralNorm_semantics` | For every real rectangular matrix and nonnegative c, actual Euclidean operator norm nonnegativity and equivalence of norm ≤ c with every-vector norm bounds. |
| `witness_full_column_rank` | Injectivity of the displayed matrix as a genuine Euclidean linear map. |
| `exact_lsmr_run` | The full explicit x₀,…,x₃ run satisfies zero start, every Krylov normal-residual minimization, minimum length, first exact termination at 3, and nonzero x₁,x₂,x₃. |
| `optimal_errors` | Existence of **attained** minima μ₁,μ₂ over all real feasible E with fixed b, their nonnegativity, and μ₁² ≤ 1979/2000, 99/100 < μ₂². |
| `approximation_values` | Existence of actual four-Penrose-law approximation values, uniqueness independent of P, nonnegativity, and both exact rational squared values. |
| `terminal_errors_zero` | The actual optimal error and stipulated approximation are both zero at x₃ despite r₃ ≠ 0. |
| `both_errors_increase` | Both strict unsquared increases at the same x₁,x₂, together with the full exact source cutoff chains for both errors. |
| `canonical_counterexamples` | `¬ OptimalErrorsNonincreasing ∧ ¬ ApproximationErrorsNonincreasing`; each original universal monotonicity property is separately refuted. |

The draft uses `Mat m n = Matrix (Fin m) (Fin n) ℝ` and
`Vec n = EuclideanSpace ℝ (Fin n)`. `spectralNorm` explicitly takes the operator
norm of `A.toEuclideanLin.toContinuousLinearMap`, so it does not inherit an
accidental matrix norm. `Feasible` uses the negative of the source's displayed
normal-equation vector, which has exactly the same zero set. `IsOptimalError`
is `IsLeast errorSet`; `IsApproximation` includes x ≠ 0, the exact-LS zero
branch, and an existential P satisfying all four Penrose laws. The exported
uniqueness clauses force a single actual approximation value at each witness.

`IsLSMRIterate` explicitly quantifies over the whole Krylov submodule and
compares both normal residual and, among its minimizers, length.
`IsTerminatingLSMRRun` includes every index from zero to the first exact
least-squares iterate. Both monotonicity propositions retain arbitrary m,n,N,
A,b and all such runs; they compare adjacent indices with both iterates
nonzero. The explicit adjacent pair 1,2 lies strictly before termination.

**Draft boundary correspondence verdict: PASS at this preparation stage.** No missing domain,
norm substitution, algorithmic weakening, attainment omission, or lost paired
claim was found. This verdict covers the current bytes; hashes are recorded in
`IE-17-source-hashes.json` under `draft_boundary`. The numerical simplifications
in §§4.1 and 5.1 are auxiliary proof certificates, not replacements for any of
these eight target statements.
This is not an independent final referee approval of the eventual implementation;
this agent may implement auxiliary certificates after the proof gate opens.

Implementation will still need the actual Penrose/projector-to-rational-formula
bridge and attained-minimum existence at the counterexample. These can be
internal lemmas, specialized where useful; no unnecessary generic export is
required to complete the frozen target.

It is legitimate to specialize difficult optimization lower-bound or explicit
certificate lemmas to m = 4,n = 3. It is not legitimate to specialize away the
universal problem's domain, replace LSMR by a list with no minimizing semantics,
define μ by the displayed bounds, or define μ̃ by its rational evaluation.

The source also records an orthogonally scaled dense variant obtained with
the 4×4 Hadamard matrix Q satisfying QᵀQ = 4I:

```
A' = [[1,6,5],[1,−6,5],[1,6,−5],[1,−6,−5]],
b' = (14,10,10,10).
```

It has the same iterates and both errors doubled. This is supplementary to the
canonical negative target; the complete original manuscript remains preserved
even if the formalization does not export this optional variant. Metadata must
state the verified scope truthfully and preserve original proof attribution.

Before status promotion: independently review the frozen boundary and these
new auxiliary certificates; implement and independently review the full proof;
run the pinned kernel-only build and permitted-axiom checks; run Lean4
Comparator against the reviewed statements; run clean reproducible Linux/CI
verification; and publish the separate reviewed IE-17 PR. At this stage no
formal verification, Comparator result, or completion status is claimed.

## 9. Independent exact reconstruction record

Adjacent files:

- `IE-17-independent-check.py`: a fresh standard-library `fractions.Fraction`
  reconstruction with no imported repository checker code.
- `IE-17-independent-check.json`: complete computed matrices, all iterates,
  Gram systems and determinants, norms, D matrices, the rational E,
  original determinant certificates, exact LDL, both new diagonal-dominance
  certificates, and both approximation fractions.
- `IE-17-source-hashes.json`: current canonical/source/review SHA-256 hashes.

For the repository review copy, place the checker at
`linear-systems-and-elimination/IE-17/lean/reviews/initial-exact-check.py`
(and its generated JSON beside it). From the IE-17 `lean/` directory reproduce
with

```sh
python3 reviews/initial-exact-check.py
```

The staging original remains `IE-17-independent-check.py` in the temporary
review directory; this publication filename change does not change its bytes.
Preserve `IE-17-source-hashes.json` unchanged when copying the review records.

The checker solves the Krylov normal equations from the integer A,b, derives E
from the manuscript's compact rational construction, checks perturbation
feasibility, reconstructs each positivity certificate, and asserts the exact
inequalities. Its final result is PASS. This is an independent pre-proof
arithmetic validation; only the future Lean kernel proof can certify the
quantified analytic and algorithmic statements.
