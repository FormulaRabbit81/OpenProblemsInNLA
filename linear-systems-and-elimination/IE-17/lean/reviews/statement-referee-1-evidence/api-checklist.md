# IE-17 independent API and semantic checklist

Reviewer: OpenAI GPT-6 Codex agent `/root/reference_api_review` (AI), 2026-09-15. This is bounded read-only source/API research, independent of the upcoming statement author. No definitions or proofs were authored or compiled for IE-17; this report is not statement approval or formal verification.

## Frozen source examined

- Canonical `linear-systems-and-elimination/IE-17/README.md`: SHA256 `53cba6429e84e1c8e055e10e5b7093f03ee0d1a94c8bf57f30ed150ae4cc08dc`.
- `references/colbrook-recovered-2026-09-11/manuscripts/IE-17.tex`: SHA256 `d0e446f7b9ee5669c1beece9ca91a89387b2f8e340c19bca8254f556386efbcd`.
- Mathlib source read from the IE-15 pinned dependency checkout, revision `0df444a360eaa60ab8c11dca51a86af692955474`, Lean 4.33.1. All API recommendations below refer to these actual bytes, not current upstream HEAD.

## 1. Complete mathematical boundary

The negative target requires **both** errors to increase at two consecutive nonzero exact LSMR iterates with fixed right-hand side. The concrete real matrix is `diag(1,6,5)` with a fourth zero row, and `b=(11,1,1,1)`. Its first two iterates are

- `x1=(11231,6126,5105)/31201`;
- `x2=(87659,7599,16865)/55219`.

The run starts at zero, minimizes the **Euclidean normal residual** over the actual Krylov subspace, uses the minimum-length minimizer if necessary, and terminates at `x3=(11,1/6,1/5)`. It is not enough to check numerical vectors without their Krylov membership and minimization properties. Full column rank makes the relevant minimizers unique; the tie convention is therefore satisfied, rather than omitted. Check that steps 1 and 2 precede termination and are nonzero. Do not define an approximation at `x0=0`, where the canonical displayed formula is undefined.

Required quantitative conclusions are `μ(x1)^2 ≤ 1979/2000 < 99/100 < μ(x2)^2` and `μtilde(x1)^2 < 503/500 < 1007/1000 < μtilde(x2)^2`. Nonnegativity bridges these square comparisons to the actual strict increases. At an exact least-squares solution the stipulated zero branch must test `Aᵀ(b-Ax)=0`, not `b-Ax=0`.

## 2. True Euclidean matrix operator norm

Use the explicit scope `Matrix.Norms.L2Operator` from [Analysis/CStarAlgebra/Matrix.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/CStarAlgebra/Matrix.lean). The matrix norm under this scope is the operator norm induced by EuclideanSpace, including rectangular matrices. The source explicitly preserves the ordinary finite matrix topology.

APIs read:

- `Matrix.l2_opNorm_def` (line 185) identifies the norm with the continuous linear map obtained from `Matrix.toEuclideanLin` and `LinearMap.toContinuousLinearMap`.
- `Matrix.l2_opNorm_conjTranspose` (191): adjoint preserves the norm.
- `Matrix.l2_opNorm_conjTranspose_mul_self` (199): `‖Aᴴ*A‖=‖A‖*‖A‖`.
- `Matrix.l2_opNorm_mulVec` (209) and `Matrix.l2_opNorm_mul` (217).
- `Matrix.toEuclideanCLM` and `l2_opNorm_toEuclideanCLM` are square-matrix APIs; use `toEuclideanLin` for the rectangular 4-by-3 and 7-by-3 matrices.
- `ContinuousLinearMap.opNorm_le_bound` and `ContinuousLinearMap.le_opNorm` supply the universal-vector upper and individual-vector lower bounds.

Vectors must be `EuclideanSpace ℝ (Fin n)` or explicitly transported using `WithLp.toLp 2` / `EuclideanSpace.equiv`. Plain functions `Fin n → ℝ` use a supremum norm. **A mere type ascription on `A *ᵥ x` can still select the wrong norm**: this is explicitly warned about beside `l2_opNorm_mulVec`. Review elaborated signatures and helper definitions, not notation alone.

In [PiL2.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/PiL2.lean), `Matrix.toEuclideanLin` is the rectangular `toLpLin 2 2` abbreviation. Prefer current `toLpLin_apply`, `ofLp_toLpLin`, and `toLpLin_toLp`; several older specialized apply lemmas are deprecated.

## 3. Moore–Penrose semantics and available projection APIs

Repository searches for `Moore.Penrose`, `pseudoInverse`, `pseudoinverse`, and `pinv` located no Moore–Penrose implementation. `Matrix/NonsingularInverse.lean` explicitly excludes pseudoinverses from its scope. Therefore do not silently treat its total square inverse as a Moore–Penrose inverse.

An honest relation-based boundary may require the four Penrose equations for rectangular `K` and `B`:

1. `K B K = K`;
2. `B K B = B`;
3. `(K B)ᵀ = K B`;
4. `(B K)ᵀ = B K`.

Then define the nonzero-iterate approximation by existence of such a `B` and the **actual** Euclidean norm `‖K B v‖/‖x‖`. This must be accompanied by existence at the needed matrices and uniqueness of the resulting value. Proving uniqueness of `K B` among Penrose witnesses is sufficient; a general uniqueness theorem for `B` is optional. Existential convenient witnesses alone should not leave a multivalued error relation at the comparison boundary.

The projection API gives a reusable bridge. [Projection/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean) has:

- `Submodule.orthogonalProjectionOnto` (113), valued in the subspace subtype;
- `Submodule.starProjection` (125), the ambient-valued continuous linear map;
- `eq_starProjection_of_mem_of_inner_eq_zero` (173) and `eq_starProjection_of_mem_orthogonal` (185), giving projector uniqueness from membership and orthogonal residual;
- `starProjection_minimal` (220), the distance-minimization property;
- `HasOrthogonalProjection.ofCompleteSpace` (59). Finite-dimensional subspaces are complete/closed, giving the needed instance.

If using `B=(KᵀK)⁻¹Kᵀ`, prove invertibility of the Gram matrix and the Penrose equations. For this example residuals are nonzero (their fourth coordinate is one), hence `η=‖r‖/‖x‖>0` at the two compared iterates. This alone makes the vertical block `K=[A;ηI]` injective; the original `A` is also full column rank. Useful actual APIs:

- `Matrix.ker_mulVecLin_transpose_mul_self` and its conjugate-transpose analogue in `LinearAlgebra/Matrix/Rank.lean` (around 537 and 499);
- `Matrix.mulVec_injective_iff_isUnit` in `NonsingularInverse.lean` (360), for the square Gram matrix;
- `Matrix.PosDef.isUnit` and `Matrix.PosDef.inv` in `LinearAlgebra/Matrix/PosDef.lean` (507 onward).

The exact rational expression for the approximation's **square** removes square-root work after the projector bridge. It must be proved equal to the canonical norm formula; labeling the rational expression as the error without that equality would weaken correspondence.

## 4. Attained spectral perturbation minimum

`IsLeast {‖E‖₂ | (A+E)ᵀ((A+E)x-b)=0} μ` is an appropriate boundary and expresses the canonical actual minimum without a default value for an empty infimum. If using `sInf`, separately bridge it to an attained minimizer.

The feasible set is nonempty (`E=-A`), and is closed because the normal-equation map is continuous. Restrict to the closed operator-norm ball of radius `‖A‖₂`; this intersection is nonempty and compact in the finite-dimensional real matrix space. Its norm minimizer is global since all excluded feasible matrices have larger norm than `-A`.

Actual APIs:

- `FiniteDimensional.proper_real` in [Analysis/Normed/Module/FiniteDimension.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Module/FiniteDimension.lean), line 562; `Metric.isCompact_closedBall` and compact intersection with a closed set.
- `IsCompact.exists_isMinOn` in [Topology/Order/Compact.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Order/Compact.lean), line 230.
- `ContinuousOn.exists_isMinOn'` (254) is an alternative coercive-on-a-closed-set route.
- `IsCompact.exists_forall_le'` (238) converts a continuous pointwise strict lower bound on a compact set to a uniform strict gap.

**Strictness gate:** a proof that every feasible `E` satisfies `99/100 < ‖E‖₂²` alone does not imply strict inequality for its infimum. An actual minimizing `E`, or a proved uniform spectral gap, is needed.

For the lower-bound source argument the perturbed zero-residual case needs separate treatment. In this concrete example the fourth coordinate basis vector has unit Euclidean norm and lies in `ker Aᵀ`; this avoids general dimension/rank machinery without weakening the counterexample. For the nonzero-residual case normalize the actual perturbed residual, not the original one.

## 5. Finite Krylov minimization

No `Krylov` or `krylov` API was located by full Mathlib source search. A finite `Submodule.span` of the actual powers `H^j g`, with `0≤j<k`, matches the canonical definition. Concrete column maps `V1=[g]`, `V2=[g,Hg]`, `V3=[g,Hg,H²g]` may simplify proofs, provided equality with that span is proved.

For each candidate, prove membership and `(H V_k)ᵀ(g-Hx_k)=0`. Then the normal residual decomposes orthogonally for every competing vector. [InnerProductSpace/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/Basic.lean) provides `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` (564), with multiplication-form squares. Injectivity of `H` on the span gives uniqueness and therefore minimum length. Alternatively project `g` onto the finite-dimensional image of the Krylov subspace under `H` and pull back using injectivity.

Do not encode minimization only among the displayed basis vectors or only among rational coefficients: the canonical competitors are all real vectors in the Krylov span.

## 6. Computation and referee plan

The rational perturbation `E` at the end of the manuscript avoids formalizing the entire general matrix-completion theorem. Prove its exact normal equations and `‖E‖₂²≤1979/2000`. The latter still requires an honest bridge from positive semidefiniteness of `κI-EᵀE` to the Euclidean operator norm. For the lower bound, exact positive definiteness of the supplied 4-by-4 rational matrix is enough. Searches did not locate a ready-made Sylvester leading-principal-minor criterion in the searched Matrix modules; an explicit LDL/sum-of-positive-squares factorization is a plausible smaller kernel proof. Do not replace spectral bounds with a Frobenius or entrywise bound unless it proves the exact required inequality.

LeanCert should consume an exact rational inequality essential to the target, explicitly in kernel mode. Full proof closure must subsequently pass the campaign's permitted-axiom and real Linux Comparator checks; this API audit asserts neither. Mathematical Definitions, numerical dossier, and Challenge must receive independent exact-byte statement reviews before proof implementation. Preserve IE-17 identity, complete original statement, and Matthew J. Colbrook's original proof attribution; the requested George Stepaniants/Caltech formalization credit is additional attribution.
