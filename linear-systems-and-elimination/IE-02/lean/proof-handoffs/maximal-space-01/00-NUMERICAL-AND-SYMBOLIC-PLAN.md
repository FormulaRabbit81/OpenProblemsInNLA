# IE-02 maximal-space norm: numerical and symbolic plan

Prepared before proof source is written. Scope: exactly frozen contract 7,
`maximal_space_norm`; this is not the whole IE-02 target or an independent review.

## Exact semantic target

For every natural dimension n, including 0, and every complex n-by-n matrix A,
let L be the actual complex Euclidean matrix map and M its continuous operator
norm. The frozen maximalSpace is the kernel of L†L - (M² : ℂ) I. Prove that
this submodule is closed and, for every x, membership is equivalent to
‖L x‖ = M ‖x‖. There is no positive-dimension, invertibility, simple-eigenvalue,
nonzero-matrix, or nonzero-vector hypothesis. All complex entries and all
multiplicities of the maximal singular value are retained.

The numerical quantities are the actual nonnegative norms M, ‖x‖ and ‖Lx‖.
The only scalar operations in the proof are squares and, after explicitly
excluding x = 0, division by ‖x‖². No interval computation or new LeanCert
numerical certificate is needed. The existing project certificate remains the
single separately planned descent certificate; this module has kernel trust
assertions but does not manufacture a numerical computation.

## Symbolic route

1. Finite-dimensional submodules are closed. Apply Mathlib's
   Submodule.closed_of_finiteDimensional directly to the frozen submodule.
2. Set G = L.adjoint ∘ₗ L and T = G.toContinuousLinearMap. The adjoint identity
   gives T.reApplyInnerSelf y = ‖L y‖². The frozen kernel condition is precisely
   G x = (M² : ℂ) • x. Document every representation-only `change`.
3. From membership, take the real part of the inner product with x. The scalar
   M² is real, so the result is ‖Lx‖² = M² ‖x‖². The two sides whose squares
   agree are nonnegative; deduce the required norm equality.
4. Conversely, treat x = 0 by linearity. For x ≠ 0, the operator-norm bound and
   the assumed equality show that x globally maximizes T.reApplyInnerSelf on
   the sphere of radius ‖x‖. Gram symmetry gives IsSelfAdjoint T. Invoke pinned
   IsSelfAdjoint.eq_smul_self_of_isLocalExtrOn after localizing that maximum.
5. The Rayleigh quotient at x equals M²: expand the energy, use the assumed
   equality, and cancel the nonzero denominator ‖x‖². This produces exactly
   the frozen kernel equation. No spectral theorem, SVD, minimax, norm
   attainment existence, or positive-semidefinite square-root oracle is added.

The zero-dimensional case needs no separate nontriviality instance: its sole
vector is handled by the same zero branch. For A = 0 all vectors satisfy both
sides. A repeated maximal singular value imposes no choice of eigenbasis.

## Primary pinned reuse

Mathlib pin 0df444a360eaa60ab8c11dca51a86af692955474 is read-only.
- Analysis/InnerProductSpace/Rayleigh.lean: the exact local-extremum-to-eigenvector
  theorem (line 258), and the Rayleigh quotient definition. Central library
  authors credited: Heather Macbeth and Frédéric Dupuis.
- Analysis/InnerProductSpace/Adjoint.lean: adjoint_inner_left,
  isSymmetric_adjoint_comp_self, isSelfAdjoint_iff_isSymmetric.
- Analysis/InnerProductSpace/LinearMap.lean: reApplyInnerSelf_apply.
- Analysis/InnerProductSpace/Defs.lean and Basic.lean: real-scalar inner product
  and norm-square identity; Analysis/RCLike/Basic.lean: re_mul_ofReal.
- Analysis/Normed/Operator/Basic.lean: actual le_opNorm.
- Topology/Algebra/Module/FiniteDimension.lean: closed_of_finiteDimensional.
- Topology/Order/LocalExtr.lean: IsMaxOn.localize.
- Algebra/Order/GroupWithZero/Basic.lean: sq_eq_sq₀ and sq_le_sq₀.
- Algebra/GroupWithZero/Defs.lean: mul_div_cancel_right₀.

Existing MI-13 CommutatorMaximum.lean was inspected only for its compatible
Gram-energy/continuous-wrapper representation. It is not imported and provides
no assumed mathematical result to this module.

## Authorization and verification boundary

Root acceptance IE02-ROOT-FREEZE-ACCEPTANCE.json authorizes proof development
against the 13 frozen inputs. This child writes only the new MaximalSpace.lean
and this new handoff, never changes frozen inputs, and runs no Lean compiler,
Lake, cache mutation, Git, or network. Root alone performs later local Lean
checking. At plan time the candidate module does not exist. Later source
metadata must remain explicitly unrun until root produces an actual receipt.
Attribution is George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; no email, prior credits retained.
