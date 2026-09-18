# Pinned primary API evidence

All paths below are relative to the read-only Mathlib/ directory at pin
0df444a360eaa60ab8c11dca51a86af692955474. Whole-file SHA-256 bindings were taken
before coding in 01-PRE-CODE-BINDINGS.json and rechecked at seal. The signatures
and adjacent proofs were read directly. Cached Rayleigh and FiniteDimension
source/olean files exist; existence alone is not an output provenance or build
claim. No compiler or cache command ran.

| Source and line | Actual reused API / role |
| --- | --- |
| Analysis/InnerProductSpace/Rayleigh.lean:56 | `ContinuousLinearMap.rayleighQuotient` is real Gram energy divided by the squared norm. |
| Analysis/InnerProductSpace/Rayleigh.lean:258 | `IsSelfAdjoint.eq_smul_self_of_isLocalExtrOn` turns a local energy extremum on the sphere of radius norm x into `T x = (T.rayleighQuotient x : 𝕜) • x`. Assumes CompleteSpace, not Nontrivial or a chosen eigenbasis. |
| Analysis/InnerProductSpace/Adjoint.lean:581 | `LinearMap.adjoint_inner_left` identifies the Gram quadratic form with the output inner product. |
| Analysis/InnerProductSpace/Adjoint.lean:756 | `LinearMap.isSymmetric_adjoint_comp_self` supplies Gram symmetry. |
| Analysis/InnerProductSpace/Adjoint.lean:380 | `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric` transports symmetry to the continuous wrapper. |
| Analysis/InnerProductSpace/LinearMap.lean:268 | `ContinuousLinearMap.reApplyInnerSelf_apply` exposes the real part of `inner (T x) x`. |
| Analysis/InnerProductSpace/Defs.lean:304 | `inner_smul_ofReal_left` handles the real M² scalar in the first, conjugate-linear inner-product slot. |
| Analysis/InnerProductSpace/Basic.lean:53 | `norm_sq_eq_re_inner` is exported from InnerProductSpace; it identifies the real self-inner product with the squared norm. |
| Analysis/RCLike/Basic.lean:226 | `RCLike.re_mul_ofReal` extracts the real scalar without treating arbitrary complex order as real order. |
| Analysis/Normed/Operator/Basic.lean:237 | `ContinuousLinearMap.le_opNorm` bounds the actual Euclidean output norm by operator norm times input norm. |
| Topology/Algebra/Module/FiniteDimension.lean:530 | `Submodule.closed_of_finiteDimensional` proves closedness in the finite-dimensional Hausdorff Euclidean space, including dimension zero. |
| Topology/Order/LocalExtr.lean:117 | `IsMaxOn.localize` yields the local maximum needed by Rayleigh. |
| Algebra/Order/GroupWithZero/Basic.lean:705,715 | `sq_eq_sq₀` and `sq_le_sq₀` justify precisely the nonnegative square comparisons. |
| Algebra/GroupWithZero/Defs.lean:208 | `mul_div_cancel_right₀` cancels the explicitly nonzero squared norm in the Rayleigh quotient. |

The three `change` steps in the candidate are each commented: two merely expose
the continuous extension as its underlying Gram map, and one expands the
frozen kernel plus scalar identity action. They introduce no mathematical
identification assumption. The actual `change` elaboration and instance
transport remain for root's local compiler to verify.

No local duplicate of a spectral theorem, matrix square-root theorem, or
maximal-space characterization is introduced. The only local assertions are
energy, kernel membership, square identity, self-adjointness, energy maximum,
and Rayleigh-value calculations used immediately in the single contract.
