# SP-15 coefficient identity and strict derivative: pre-code plan

Prepared by `/root/mi13_full_referee2`. This plan concerns exact frozen contracts 7 and 9 only. The statement freeze has already been accepted, but this implementation batch awaits separate coordinator acceptance. No Lean proof for these two contracts is included or claimed here.

The source boundary is `NLA/SP15/Definitions.lean` at SHA-256 `fa57c71cd3e6d6551f081e479121f9f6a4695858732f3e6d1fa4cd79ad927498`, with the exact contract headers retained in `EXACT-HEADERS.json`. The existing numerical LU certificate alone does not identify a derivative. The present bridge must prove that identification from the actual coefficient functions, including all ten input coordinates.

## Numerical and symbolic obligations fixed before proof

For arbitrary `x : Fin 10 → ℝ` and arbitrary complex `u,s`, let `pᵢ = x(i-1)`, `qᵢ = x(i+2)`, `a=x6`, `b=x7`, `c=x8`, and `d=x9`. Define, for this explanation only,

`Sᵢ = s + pᵢ`, `Dᵢ = u + s(pᵢ+qᵢ) + pᵢqᵢ`, and `E=c²+d²`,

with real scalars coerced into ℂ. The determinant of the actual matrix `uI+s(P+Q)+PQ` must equal

`D₁D₂D₃ - E S₂S₃D₁ - b² S₁S₃D₂ - a² S₁S₂D₃ + 2abc S₁S₂S₃`.

The identity is universal; it has no box, positivity, invertibility, or real-shift restriction. It must then equal exactly `u³ + Σᵢ (coefficients x i : ℂ) * coefficientMonomials u s i`, in the frozen monomial order

`1, u, s, u², us, s², u²s, us², s³`.

The second public obligation is the actual strict Fréchet derivative at `(1,2,3,4,4,4,1,1,1,1)`. It is the concrete continuous linear map `coefficientDerivative`, defined from the full frozen 9×10 Jacobian. Its action on an arbitrary real perturbation vector `v` is the matrix-vector product by the nine complete rows:

```
 300 150 100  84  90  90  -36 -36 -36  -48
  75  57  43  20  32  36   -4  -6 -12  -12
 514 332 238 202 213 213  -78 -78 -78 -100
   4   4   4   1   2   3    0   0   0    0
  70  61  53  33  40  45   -6  -8 -10  -10
 267 205 163 158 152 148  -54 -52 -46  -58
   1   1   1   1   1   1    0   0   0    0
  13  12  11  13  12  11   -2  -2  -2   -2
  40  34  29  40  34  29  -12 -10  -8  -10
```

This is a universal linear-map identity, not merely nine or ninety checked directional samples. In particular, the final column cannot be discarded: the later augmented map uses the original tenth parameter as its free coordinate.

## Exact determinant route

1. Derive the nine entries of the actual `uI+s(P+Q)+PQ` from the concrete frozen definitions. Reuse `Matrix.diagonal_mul`, so the product `PQ` is computed as row scaling rather than nine three-term sums. The diagonal entries are `Dᵢ`; the off-diagonal entries are `Sᵢ Qᵢⱼ`. A three-by-three entry equality is the only matrix expansion needed.

2. Reuse `Matrix.det_fin_three`; never expand the nine-by-nine shifted Gram determinant here. Regroup its six terms into the five displayed factored terms. The complex pair `c+I*d` and `c-I*d` is handled with existing `Complex.mul_conj`, `Complex.normSq_add_mul_I`, and conjugation simp lemmas. Their sum reduces to `2c`. This avoids duplicating a general norm-square or complex-conjugate theorem, and removes all imaginary units before the main coefficient collection.

3. Collect coefficients only after the five-term factorization. Use the following small commutative-ring expansion identities as needed, each separately proved by `ring` under the default heartbeat limit:

   - `(u+s*r₁+t₁)(u+s*r₂+t₂)(u+s*r₃+t₃)` grouped by its ten possible `u,s` monomials;
   - `(s+p)(s+q)(u+s*r+t) = p*q*t + p*q*u + (p*q*r+(p+q)*t)*s + (p+q)*u*s + ((p+q)*r+t)*s² + u*s² + r*s³`;
   - `(s+p₁)(s+p₂)(s+p₃) = p₁p₂p₃ + (p₁p₂+p₁p₃+p₂p₃)s + (p₁+p₂+p₃)s² + s³`.

   Keep `rᵢ=pᵢ+qᵢ`, `tᵢ=pᵢqᵢ`, `E`, the two squares, and `2abc` grouped until applying these identities. Real-to-complex coercions use the existing `Complex.ofReal_add`, `ofReal_mul`, `ofReal_pow` APIs. Then unfold the actual frozen coefficient vector and its monomial vector, reduce literal lookups using the pinned `Matrix.cons_val` simproc, and use the nine-term finite sum and ring normalization to identify the exact target. There is no numerical substitution for a universal identity.

The three small generic expansions may be omitted if the factored expression closes within the default budget with a single modest ring normalization. They may not be replaced by increasing the computation allowance. Any private helper must have an actual consumer, retain the original arbitrary complex scope, and be included in source review.

## Actual strict derivative route

Use `hasStrictFDerivAt_apply` for each coordinate projection. Reuse the strict derivative constructors `.add`, `.sub`, `.mul`, `.const_mul`, and `.pow`; these directly prove strict differentiability of the actual polynomial expression. No finite differences, approximate Jacobian, imported differentiability oracle, assumed row table, or generic-rank assertion is involved.

Preserve the factored straight-line expression of each frozen coefficient. The recurring quantities have the following exact values and derivatives at the base point, where `eᵢ` is the continuous coordinate projection applied to a perturbation:

- `r₁,r₂,r₃` have values `5,6,7` and derivatives `e₀+e₃`, `e₁+e₄`, `e₂+e₅`.
- `t₁,t₂,t₃` have values `4,8,12` and derivatives `4e₀+e₃`, `4e₁+2e₄`, `4e₂+3e₅`.
- `E=c²+d²` has value `2` and derivative `2e₈+2e₉`.
- `a²,b²` have value `1` and derivatives `2e₆,2e₇`.
- `2abc` has value `2` and derivative `2e₆+2e₇+2e₈`.

Prove nine small component lemmas rather than normalize a large vector derivative in one declaration. For each component, form its strict derivative proof by the library constructors in the same operation order as the frozen coefficient expression. Reduce the fixed base-point lookups with `Matrix.cons_val` before normalizing scalars. Use `HasStrictFDerivAt.congr_fderiv` to identify the resulting continuous linear map with the corresponding projection of the concrete `coefficientDerivative`.

The linear-map equality is proved by extensionality on an arbitrary `v : Parameters`. Reuse `ContinuousLinearMap.proj_apply`, `comp_apply`, the ordinary linear-map coercion theorem for `toContinuousLinearMap`, `Matrix.mulVecLin_apply`, and `Matrix.mulVec_apply_eq_sum`. Expand only the ten-term matrix-vector sum. After applying map operations to `v`, the goal is a degree-one real polynomial identity in ten coordinates. Exact `norm_num` and `ring` suffice; no determinant, inverse, interval, or higher-order derivative is evaluated.

Finally combine all nine components with `hasStrictFDerivAt_pi'` / `hasStrictFDerivAt_pi''`. This establishes the frozen public theorem for the actual coefficient map. The completed derivative theorem is the mandatory bridge before the existing numerical minor may be used in the later inverse-function theorem.

## Resource, trust and evidence boundaries

Use separate `CoefficientIdentity.lean` and `CoefficientDerivative.lean` modules, with small private helpers if needed. Keep the default 200,000 heartbeats. Simplify literal indices before real/complex algebra, share common factored subexpressions, and split by component if an actual local timeout identifies a need. Do not introduce parallel compiler processes, caches, a Linux run, or source changes to the frozen definitions or headers.

These obligations are algebraic and differential; they need no further interval computation. The project already has a genuinely consumed kernel LeanCert radius certificate. Every new exported theorem receives `#print axioms` and `#assert_trust kernel`; root alone compiles locally, records exact hashes/logs and requests independent review before publication. No successful execution is claimed by this plan.

`prepare_evidence.py` authenticates the frozen source boundary and records primary Mathlib excerpts. Its standard-library forward-mode diagnostic evaluates the actual parsed coefficient source and compares all 90 integer derivative entries with the actual frozen Jacobian. That is planning evidence, not a Lean proof or a statement-proving oracle. The existing exact determinant-polynomial reconnaissance is retained as history and can supply operation-size information without being imported into Lean.

Credit George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, and substantial OpenAI Codex assistance. Preserve Fortier Bourque and Ransford's original mathematical attribution and the formal-library authorship. Publish no email. This batch does not establish the inverse-function fiber, positivity/square roots, all-complex-shift spectral transport, arbitrary-unitary rigidity, or the full original SP-15 target.
