# PF-02 — exact pre-proof mathematical and numerical dossier

Prepared 2026-09-15 by the campaign target-preparation agent. This is a
mathematical review and independent exact-arithmetic diagnostic, **not a Lean
verification** or final referee approval. No PF-02 proof code, canonical edit,
or status change has been made. The statement boundary must be independently
reviewed and frozen before proof implementation.

## 1. Selection, identity, attribution, and source review

**Recommended next target: PF-02**, connectedness of minimal real positive
semidefinite factorization orbits. It is currently queued in the campaign
control file. Its complete universal assertion is refuted by a single explicit
size-three factorization problem. The numerical data are small integers; the
essential nonnumerical obligation is a continuous invariant on the full actual
congruence quotient.

- Permanent canonical path:
  `nonnegative-and-positive-factorizations/PF-02/README.md`.
- Current separate worktree: `/private/tmp/nla-formalization-pf02-20260915`,
  branch `codex/lean-pf02`, published base
  `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`.
- Complete original manuscript:
  `references/colbrook-factorization-2026-09-11/manuscripts/PF-02_disconnected_orbits.tex`.
- Original proof author: **Matthew J. Colbrook, Department of Applied
  Mathematics and Theoretical Physics, University of Cambridge**.
- Requested formalization author: **George Stepaniants, Department of Computing
  and Mathematical Sciences, California Institute of Technology**. Keep these
  roles distinct; add no contact email. Preserve the original source and its
  historical attribution unchanged.
- Complete-file hashes and the distinct historical reviewed-source hash are
  recorded in `source-hashes.json`.

I read the complete manuscript, including its optional extensions to every
factor size and strictly positive perturbations, the canonical page, and the
previous independent review. **Preparation verdict: the source's Theorem 1
correctly refutes the complete canonical question; no material gap was found
in that targeted argument.** The all-size extensions are not necessary for the
negative answer. Their source remains preserved, and metadata must distinguish
them from the exact theorem proved in the proposed formalization.

The primary [Fawzi–Gouveia–Parrilo–Robinson–Thomas paper, §9.2, Problem 9.4](https://arxiv.org/html/1407.4095#S9.SS2)
poses the same quotient-connectedness question with the same maximal ordinary
rank condition. It explains why disconnected nonnegative factorizations at a
different ordinary rank do not settle this question. The proposed witness has
exactly the required rank six and PSD rank three.

## 2. Complete canonical mathematical statement

For k ≥ 1, S₊ᵏ is the cone of **real symmetric positive semidefinite** k×k
matrices. For an entrywise nonnegative real p×q matrix M, its real positive
semidefinite rank is

```
rank_psd(M) = min {k ≥ 1 : there exist A₁,…,A_p,B₁,…,B_q ∈ S₊ᵏ
                         with Mᵢⱼ = tr(Aᵢ Bⱼ) for every i,j}.
```

The full retained problem is:

> Let k ≥ 3 and p,q ≥ 1 be integers. Suppose M ∈ ℝ₊^(p×q) satisfies
>
> rank(M) = k(k+1)/2 and rank_psd(M) = k.
>
> Let F_k(M) be the set of all tuples (A₁,…,A_p,B₁,…,B_q) in
> (S₊ᵏ)^(p+q) satisfying tr(AᵢBⱼ) = Mᵢⱼ for every i,j. Give it the Euclidean
> subspace topology. Identify tuples under the changes of basis
>
> Aᵢ ↦ Sᵀ Aᵢ S,    Bⱼ ↦ S⁻¹ Bⱼ S⁻ᵀ,    S ∈ GL(k,ℝ).
>
> Give the resulting orbit space the quotient topology. Is F_k(M)/GL(k,ℝ)
> connected for every M satisfying these hypotheses?

The answer is **no**. The universal statement must retain every allowed
dimension, all real matrix entries and factors, the full real GL group of both
determinant signs, and the actual quotient topology. A size-three witness is
sufficient to negate that full statement; no universal restriction to size
three may be inserted into the original conjecture.

### 2.1 Exact definition obligations

1. Use actual `Matrix.rank` over ℝ. The ordinary-rank hypothesis is essential.
2. Define feasible sizes as `{k : ℕ | 1 ≤ k ∧ Nonempty (FactorSpace M k)}`.
   The relation `IsLeast` of this set at k is an exact attained-minimum
   formulation of PSD rank. The witness must prove both a size-three
   factorization and impossibility of every positive smaller size. An arbitrary
   supplied factorization is not evidence of minimal size.
3. `FactorSpace M k` contains **all** pairs of row/column factor families with
   each matrix real symmetric PSD and every trace equation. Row and column
   factors are independent families. Although the witnesses set Bᵢ=Aᵢ, this
   equality must not be imposed on the full factor space.
4. Positive semidefinite does **not** mean entrywise nonnegative. In particular,
   the second witness has negative off-diagonal entries and is still positive
   definite. A definition requiring entrywise nonnegative factors would change
   the target.
5. The factor topology is inherited from the finite product of real matrix
   coordinate spaces. The standard product topology is exactly the Euclidean
   topology here. It must not be replaced by a discrete topology.
6. A congruence parameter may be represented by a unit of the square matrix
   ring, with its actual inverse. This represents the full real GL group.
   No orthogonality, positivity of det S, rationality, or normalization
   restriction may be imposed.
7. The orbit relation is exactly existence of a **single** such S giving both
   displayed transformations. If `Quot` is used, prove an `orbit_eq_iff` bridge
   showing that its generated equivalence is the same actual congruence
   relation. Alternatively prove the relation is a setoid and use `Quotient`.
   Composition has the appropriate order: applying S and then T gives ST.
8. Use the coinduced quotient topology of the canonical projection. A quotient
   defined only as a set is insufficient. Prove the projection's quotient-map
   property or its explicit continuity universal property.

## 3. The full exact integer witness

Take k=3, p=q=6 and

```
M = [[24,20,20,16,16,16],
     [20,24,20,16,16,16],
     [20,20,24,16,16,16],
     [16,16,16,14,12,12],
     [16,16,16,12,14,12],
     [16,16,16,12,12,14]].
```

Every entry is a strictly positive integer, with minimum entry 12. Let Eᵢⱼ
denote a 3×3 matrix unit and set

```
A₁ = diag(4,2,2), A₂ = diag(2,4,2), A₃ = diag(2,2,4),
A₄ = [[2,1,0],[1,2,0],[0,0,2]],
A₅ = [[2,0,1],[0,2,0],[1,0,2]],
A₆ = [[2,0,0],[0,2,1],[0,1,2]],
Bᵢ = Aᵢ for i=1,…,6.
```

The second factorization changes **both** A₄ and B₄ to

```
Â₄ = B̂₄ = [[2,−1,0],[−1,2,0],[0,0,2]],
```

and leaves all other factors unchanged. For every one of the 36 index pairs,

```
tr(AᵢBⱼ) = Mᵢⱼ = tr(ÂᵢB̂ⱼ).
```

These are exact trace constraints, not entrywise products or a factorization
of M into two ordinary matrices of width three.

### 3.1 All-real positive-definiteness certificates

The following quadratic-form identities avoid computing eigenvalues. For
v ∈ ℝ³, write s=Σᵢvᵢ². The first three factors satisfy

```
vᵀ(2I+2Eᵢᵢ)v = 2s+2vᵢ².
```

For each remaining factor 2I+ε(Eᵢⱼ+Eⱼᵢ), ε ∈ {−1,1}, and the third index ℓ,

```
vᵀ(2I+ε(Eᵢⱼ+Eⱼᵢ))v = s+(vᵢ+εvⱼ)²+v_ℓ².
```

Thus each factor is positive definite for every nonzero real v. Both forms
include all twelve row-factor instances across the two tuples; the column
families duplicate them. The diagnostic independently checks these polynomial
identities. Its principal-minor computations are cross-checks, not needed for
the proposed kernel proof.

## 4. Ordinary rank and actual minimum PSD size

Use the fixed symmetric coordinates

```
coord(X) = (X₁₁,X₂₂,X₃₃,X₁₂,X₁₃,X₂₃),
G = diag(1,1,1,2,2,2).
```

For any two symmetric 3×3 matrices, not just the witnesses,

```
tr(XY) = coord(X) G coord(Y)ᵀ.
```

If U_A has the six row vectors coord(Aᵢ), the first coordinate matrix is

```
U = [[4,2,2,0,0,0],
     [2,4,2,0,0,0],
     [2,2,4,0,0,0],
     [2,2,2,1,0,0],
     [2,2,2,0,1,0],
     [2,2,2,0,0,1]].
```

The second Û has only entry (4,4) changed from 1 to −1. Exact identities:

```
det U = 32, det Û = −32, det G = 8,
M = U G Uᵀ = Û G Ûᵀ,
det M = 8192 ≠ 0, rank M = 6 = 3(3+1)/2.
```

Block-triangular determinant formulas reduce det U to the upper 3×3 diagonal
block and det Û to its negative; it is unnecessary to expand a generic
six-dimensional determinant just to establish these numerical values.

### 4.1 Cheaper minimum-size argument without changing the target

The source uses the general symmetric dimension bound
`rank M ≤ k(k+1)/2`. A simpler auxiliary bound suffices for this particular
minimum-size proof: **any** trace factorization of size k, even with arbitrary
real matrix factors, yields `rank M ≤ k²`.

Indeed flatten Aᵢ into Uᵢ,(a,b)=Aᵢ,ab and set V_(a,b),j=Bⱼ,ba. Then M=UV,
with an inner index set of cardinality k², so the usual rank-product inequality
gives the bound. For k=1 or k=2 it contradicts rank M=6. Size three is attained
by the displayed true PSD factors. This proves the exact `IsLeast` claim for
the positive feasible-size set and therefore PSD rank three. The stronger
general dimension formula is not needed or being assumed.

## 5. Every factorization has a nonzero orientation determinant

For **arbitrary** (Ã,B̃) ∈ F₃(M), let U_Ã and U_B̃ contain the corresponding
symmetric coordinate row vectors. The trace-coordinate identity gives

```
M = U_Ã G U_B̃ᵀ.
```

Taking determinants and using det M≠0 shows det U_Ã≠0 (and det U_B̃≠0).
This statement must quantify over the entire real PSD fiber, including
singular individual factors and unrelated row and column factors. Positivity
or nonsingularity of every individual factor is not required for this argument.

Define

```
ε(Ã,B̃) = det U_Ã / |det U_Ã| ∈ {−1,+1}.
```

It is well defined everywhere on F₃(M) and continuous, because the determinant
is a continuous coordinate polynomial and its absolute value never vanishes
on this whole fiber. The two displayed factorizations give ε=1 and ε=−1.

## 6. All-congruence invariance, with a fully symbolic certificate

Write an arbitrary real matrix as

```
S = [[a,b,c],[d,e,f],[g,h,i]].
```

In the coordinate order above, the matrix C(S) satisfying
`coord(SᵀXS) = coord(X) C(S)` for every symmetric X is

```
C(S) =
 [[a², b², c², ab, ac, bc],
  [d², e², f², de, df, ef],
  [g², h², i², gh, gi, hi],
  [2ad, 2be, 2cf, ae+bd, af+cd, bf+ce],
  [2ag, 2bh, 2ci, ah+bg, ai+cg, bi+ch],
  [2dg, 2eh, 2fi, dh+eg, di+fg, ei+fh]].
```

The critical identity is

```
det C(S) = (det S)⁴
```

for **every real S**, including singular ones. For an invertible congruence
matrix, it is strictly positive even if det S<0. It follows that

```
U_(SᵀÃS) = U_Ã C(S),
det U_(SᵀÃS) = det U_Ã (det S)⁴,
ε(SᵀÃS, S⁻¹B̃S⁻ᵀ) = ε(Ã,B̃).
```

The original source proves the general k-dimensional formula by a polynomial
continuation argument. The proposed formalization may specialize it to k=3
and verify this degree-twelve polynomial identity by exact algebra. This is a
legitimate simplification of an internal lemma, while the public universal
connectedness question stays unchanged.

The independent checker derives C(S) by multiplying SᵀXS for each symmetric
basis matrix; it does not merely assume the displayed coefficients. It then
expands both determinants as sparse integer polynomials in all nine variables
and compares them exactly. Each side has **120 nonzero monomials** after
collection, and equality passes. It separately verifies all six covariance
coordinates with six further independent indeterminates for X. These checks
cover a polynomial identity, not a finite sample of matrices. They remain
diagnostics until their algebraic identities are proved by Lean's kernel.

## 7. The actual quotient is disconnected

The sign invariance in §6 lets ε descend to a function ε̄ on the actual
congruence orbit quotient. The defining quotient topology gives continuity
of ε̄ from continuity of ε. This descent needs the whole congruence relation,
not only selected transformations or the two example tuples.

Either of the following equivalent finishing arguments is suitable:

- Regard ε̄ as a map into the discrete two-point space {−1,+1}. The two inverse
  images are nonempty clopen sets, disjoint and covering the quotient.
- Regard ε̄ as a real continuous map. If the quotient were connected, its image
  would be a connected real subset containing −1 and 1 and would contain 0.
  But the image lies in {−1,+1}, a contradiction.

No Hausdorff assumption on the quotient is needed. Merely exhibiting
inequivalent factors, showing an interpolation fails, or proving absence of a
path would not prove the target. The continuous separator on **every orbit**
is what establishes actual disconnectedness.

The final universal negation must instantiate k=3,p=q=6, the displayed
nonnegative M, its actual rank-six theorem, its attained PSD-rank-three theorem,
and this disconnected quotient theorem. All original quantifiers remain in
the conjecture being negated.

## 8. Exact draft boundary and implementation decomposition

I inspected the actual draft `NLA/PF02/Definitions.lean` and `Challenge.lean`
in the PF-02 worktree. The nine exported signatures below match those files.
The definitions contain no analytic or topological conclusions as assumptions:
`Factorization` is the full PSD/trace-equation subtype, `IsPSDRank` is the actual
`IsLeast` relation, and `OrbitSpace` uses Mathlib's topology on `Quot` of the
single-invertible-congruence relation. The universal conjecture retains all
original dimension, nonnegativity, ordinary-rank and minimum-size hypotheses.
The specification module has exactly nine intentional `sorry` placeholders;
none is a proof artifact or a claimed verification.

| Exact Challenge export | Exact mathematical content |
|---|---|
| `witness_data` | Every entry of `witnessM` is positive; det M=8192 and actual `Matrix.rank` M=6; the coordinate determinants of `witnessFactors 1` and `witnessFactors (-1)` are exactly 32 and −32. |
| `witness_factorizations` | `IsFactorization witnessM (witnessTuple 1)` and the corresponding −1 tuple, together with positive definiteness of every factor in each family. |
| `witness_minimal_rank` | `IsPSDRank witnessM 3`: `IsLeast {ℓ : ℕ | 1 ≤ ℓ ∧ Nonempty (Factorization witnessM ℓ)} 3`, including attainment and all smaller positive sizes. |
| `orbit_semantics` | For every dimension and every M, the actual projection is `Topology.IsQuotientMap`; for every F,G in the full factorization space, equality of their `Quot.mk` images is equivalent to the literal `Congruent F G` relation. |
| `orientation_nonvanishing` | For every F in `Factorization witnessM 3`, `orientationDet F ≠ 0`. |
| `orientation_preserved` | For every pair F,G in that whole space, `Congruent F G` implies `(0 < orientationDet F ↔ 0 < orientationDet G)`. The existential congruence ranges over all real invertible matrices. |
| `quotient_separation` | A function from the entire actual `OrbitSpace witnessM 3` to `Bool` exists and is both continuous and surjective. `Bool` has its standard discrete topology, giving a genuine two-point separator. |
| `witness_disconnected` | `¬ IsConnected (Set.univ : Set (OrbitSpace witnessM 3))`, in the actual quotient topology. |
| `canonical_counterexample` | `¬ AllMinimalOrbitsConnected`, negating the full original universal claim. |

In the reviewed boundary the sign separator is represented by `Bool`, rather
than the equivalent ±1-valued real function used to explain the source proof
in §§5–7. The intended value is `decide (0 < orientationDet F)` on a
representative. Nonvanishing, continuity of the determinant and congruence sign
preservation give a continuous quotient map; the two exact witness determinants
make both Boolean values occur. This encoding changes no topology or scope.

The full congruence-preserves-PSD-and-traces bridge and the symbolic identity
`det C(S)=(det S)^4` are required internal proof obligations, even though they
need not be separate public exports. In particular `orientation_preserved`
cannot be justified by checking the two witnesses alone. `orbit_semantics`
must prove the relation is reflexive, symmetric and transitive so that the
quotient's generated equivalence equals a single actual invertible congruence.

Suggested implementation responsibilities after the proof gate opens:

1. Exact data, PSD quadratic identities, trace-coordinate identities, det U,
   det M and the all-nine-variable congruence determinant identity.
2. Generic trace-factor rank bound, minimum feasible size, full-factor-space
   coordinate invertibility, congruence/setoid and topology bridges.
3. Continuous sign descent, surjectivity onto `Bool`, disconnectedness, and
   final exact Challenge wrappers.

Do not assume the analytic or topological conclusions in definitions. Avoid
making the whole factor space a pair of witness factorizations, requiring row
and column factors to coincide, requiring factors to be positive definite, or
restricting congruences to a smaller group.

## 9. Reuse and missing-library assessment

The pinned campaign Mathlib provides the main building blocks; no new analytic
norm or spectral-function machinery is needed for this target.

- `Mathlib/LinearAlgebra/Matrix/PosDef.lean`: actual `Matrix.PosSemidef` and
  `Matrix.PosDef`; real Hermitian means symmetric. Useful declarations include
  `PosSemidef.conjTranspose_mul_mul_same`,
  `PosSemidef.mul_mul_conjTranspose_same`, and quadratic-form criteria.
- `Mathlib/LinearAlgebra/Matrix/Rank.lean`: `Matrix.rank_mul_le_left`,
  `rank_mul_le_right`, `rank_le_card_width`, `rank_le_card_height`, and
  `rank_of_det_ne_zero`. Flattened trace factors give the sufficient k² bound.
- Matrix determinant and block APIs supply `det_mul`, `det_transpose`, and
  `det_fromBlocks_zero₂₁`/the corresponding triangular-block result. These
  avoid unnecessary six-by-six determinant enumeration for the constant data.
- `Mathlib/Topology/Instances/Matrix.lean`: `Continuous.matrix_det`, transpose
  and coordinate continuity. Use the actual finite product topology.
- `Mathlib/Topology/Constructions.lean`: the actual quotient topology,
  `continuous_quot_mk`, `continuous_quot_lift`, and
  `isQuotientMap_quotient_mk'`. A `Quot` encoding still needs an exact
  relation/equality bridge; a `Quotient` encoding needs the genuine setoid.
- `Mathlib/Topology/Connected/Basic.lean`: continuous-image connectedness
  (`IsPreconnected.image`, `IsConnected.image`). The real interval/connected
  image theorem or standard two-point discrete-space lemmas finish the
  separation argument.

No existing general determinant formula for the symmetric-square congruence
representation was located. The specialized exact six-by-six coordinate
identity above is small enough to prove directly, without developing general
representation theory or polynomial continuation from diagonalizable matrices.
The tuple/orbit definitions and their bridges appear to need local definitions,
but their topology must use Mathlib's existing quotient construction.

The established LeanCert kernel mode and permitted-axiom/Comparator harness
should be reused. The proposed minimal LeanCert kernel certificate is the exact
closed numerical assertion `0 < (32 : ℝ)`. It must be genuinely consumed with
the witness determinant equality to obtain positive orientation and the positive
side of the quotient separator's surjectivity. This is a small exact numerical
certificate; no interval partition or floating-point search is necessary. The
nine-variable determinant identity and the quantified algebra/topology require
ordinary kernel proofs. LeanCert's presence does not itself certify these
separate mathematical obligations. Independent statement and numerical review still must
precede implementation, and final independent proof reviews plus real Linux
reproducibility must precede status promotion.

## 10. Scope and diagnostic records

The original manuscript additionally proves disconnected examples in every
odd factor size and then every k≥3, including existence of positive rational
perturbations. The proposed formalization proves the complete canonical
**negative universal answer** using the explicit size-three witness. It does
not claim the optional general-size extensions, their perturbation thresholds,
or a classification of the number of components. Preserve the whole original
source and disclose this exact scope in metadata.

Files in this preparation directory:

- `source-hashes.json`: immutable canonical/source/review hashes.
- `independent-exact-check.py`: fresh standard-library checker; no imported
  repository verification code or Lean proof implementation.
- `independent-exact-check.json`: every factor, matrix and determinant,
  positivity cross-checks, and all 120 terms of the congruence determinant
  polynomial, with the diagnostic scope stated explicitly.

Run `python3 independent-exact-check.py` from this directory. It returns PASS
for both factorizations, twelve positivity sum-of-squares identities, all
constant determinants and the symbolic congruence identity. These arithmetic
records do not certify all-factorization minimality, quotient topology,
continuity, or disconnectedness. Those remain necessary Lean proof obligations.
