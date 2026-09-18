# Proposed bounded batch: normalized residuals and GMRES extrema

PLAN ONLY. Await root approval of this two-contract scope before implementing
any new Lean module. No compiler, cache mutation, Git or network is run here.
The currently queued MaximalSpace, DescentGap and WeightedCoefficients sources
are outside this batch; they will not be edited as part of it.

## Exact frozen targets and numerical meaning

Implement contract 47, normalized_polynomial_residuals, and contract 49,
gmres_extrema_semantics, with their exact frozen headers. Proposed modules are
PolynomialResiduals.lean and GMRESSemantics.lean. Contract 46 already has root's
JordanDirections proof and will not be reimplemented. The frozen inventory
contains no separately stated Jordan divisibility or remainder contract.
These two stated bridges require only finite coefficient expansion and
attainment of the resulting finite affine family.

Contract 47: for every n,k and complex lam, actual polynomial evaluation at
lowerJordan(n,lam), for all complex degree-at-most-k polynomials with p(0)=1,
is exactly the affine residual family I - sum_j c_j A^(j+1), where j ranges
over Fin k and A=lowerJordan(n,lam). Both witness directions are required.
No nonzero-lam, positive-dimension, independence-of-powers, or injectivity
hypothesis may be added to this bridge. Its use in the final canonical theorem
will retain the original n>=2, lam!=0 and 1<=k<n assumptions unchanged.

Contract 49: for every complex square matrix A, every natural k, and every
vector x, prove actual polynomial attainment of the operator-norm infimum and
of the Euclidean residual-vector-norm infimum, each with its universal
minimality property. For unit x, prove 0 <= gmresInner A k x <= idealGMRES A k.
The sInf sets and Euclidean/operator norms keep their frozen definitions.
No worst/ideal equality, minimax theorem, or extremum-existence assumption is
inserted. This contract is valid for n=0 and k=0 as well.

The numerical quantities are the actual residual norms and their attained
infima. Only a finite coefficient sum, exact real inequalities and the
existing finite-dimensional minimum theorem are needed. There are no interval
computations, eigenvalue approximations, divisions, new LeanCert certificates,
or non-symbolic computations whose size grows with n or k.

## Common symbolic parameterization

Prove a supporting result for arbitrary Square n matrix A, with R_j=A^(j+1),
and arbitrary k. This is the same two-direction residual parameterization as
contract 47 before specializing A to lowerJordan. It is independently useful
for contract 49 and makes dependent or zero powers harmless.

Forward direction: from Admissible k p obtain p.natDegree <= k and coeff p 0=1.
The pinned aeval_eq_sum_range' at length k+1 writes p(A) as
  sum_{i=0}^k p_i • A^i.
Split the constant term and reindex the tail by Fin k. Choose c_j=-p_(j+1).
Then p(A)=I-sum_j c_j • A^(j+1), including k=0. Coefficients remain complex.

Reverse direction: given c, choose
  p = 1 - sum_{j:Fin k} C(c_j) * X^(j+1).
Each term has degree at most j+1 <= k, so the finite sum and the subtraction
from 1 have degree at most k. At X=0 all positive powers vanish, giving p(0)=1.
The algebra hom aeval preserves subtraction, finite sums, constants and powers,
so its evaluation is exactly the requested affine residual. No uniqueness of
c or polynomial modulo a minimal polynomial is needed for the two existentials.

Specialize this common result to lowerJordan to discharge contract 47; unfold
only the frozen jordanDirections wrapper with a documented representation step
if elaboration requires one.

## Attainment and exact infimum correspondence

For general A, show by both witness directions that the set of admissible
polynomial residual matrices equals the finite affine residual family.
Consequently, applying the actual operator norm yields exactly the same set
of real values as the range in affineIdeal; applying the actual Euclidean
matrix action at x yields the range in affineInner. Prove these set equalities
by elementwise witnesses, then rewrite sInf. Do not replace the definitions
of idealGMRES or gmresInner by a desired equality.

Reuse affine_operator_minimum for Y=I and R_j=A^(j+1). Transport its minimizing
coefficient vector to the explicit admissible polynomial above. Its universal
minimality applies to every admissible polynomial via the forward direction.
Reuse affine_vector_minimum identically for each x. This yields both witnesses
and the exact frozen sInf equalities. No uniqueness or full-rank requirement is
introduced.

For the last inequality, the vector minimizer's norm is nonnegative. Compare
its value with the operator-minimizing polynomial evaluated at unit x, then
apply ContinuousLinearMap.le_opNorm and the exact norm-one hypothesis. The
operator witness has norm idealGMRES by the already derived set correspondence.
This avoids separate generic infimum lower-bound machinery and uses the actual
attaining witnesses. At n=0, the unit-sphere quantified implication is vacuous;
the two attained infimum statements still give zero residual values. At k=0,
the polynomial is 1 and the affine coefficient family is the empty sum.

## Primary source reuse and ownership

Mathlib pin 0df444a360eaa60ab8c11dca51a86af692955474:
- Algebra/Polynomial/AlgebraMap.lean:523 aeval_eq_sum_range', with actual algebra
  evaluation, and :290-302 aeval_X, aeval_C, aeval_monomial, aeval_X_pow;
- Algebra/Polynomial/Eval/Coeff.lean:57 coeff_zero_eq_eval_zero;
- Algebra/Polynomial/Degree/Defs.lean:142 degree/natDegree comparison,
  :330 fixed-bound addition, :365 natDegree_C_mul_X_pow_le, :526-538 subtraction;
- finite range/Fin sum reindexing, with constant term split at index zero;
- Analysis/Normed/Operator/Basic.lean:237 ContinuousLinearMap.le_opNorm;
- algebra-hom map_sub/map_sum/map_pow and the standard scalar embedding as c•1.

Project AffineMinima.lean supplies both actual affine minima at the frozen
norm semantics and permits n=0, k=0 and dependent/zero directions. Its source
is read and hash-bound. No new proof of closed-set nearest points is planned.
This batch does not need to import Toeplitz or NilpotentInverse: their algebra
is for a narrower matrix family, while these exact residual/attainment bridges
hold for arbitrary A. Only genuinely used dependencies will be imported.

Retain all 13 frozen inputs, pins, kernel trust settings, original attribution,
and George Stepaniants' Department of Computing and Mathematical Sciences,
California Institute of Technology affiliation, without email. This document
is the prospective proof author's plan, not independent proof review or an
executed verification result. Root approval, then source writing, then actual
root-only local checking and independent review remain separate steps.
