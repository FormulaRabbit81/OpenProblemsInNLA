# SF-01 exact numerical and semantic boundary

The target is the full original all-dimension, all-iteration theorem. These obligations are written before any proof implementation. The Challenge's 24 holes are specification placeholders only.

| Object or range | Exact meaning and required result |
|---|---|
| n | Every natural n>=1; no fixed dimension or enumeration. |
| A | Every real n by n matrix whose comparison equals sI-B for some entrywise nonnegative real B and s greater than the maximum modulus of B's **complex** eigenvalues; every A_ii>0. A itself need not be nonnegative, symmetric, normal or diagonalizable. |
| Comparison | Diagonal abs(A_ii), off-diagonal -abs(A_ij), with the canonical labels preserved. |
| Spectral radius | sSup of the norms of the complex algebraic spectrum. Prove finite nonempty spectrum, nonnegativity, attainment and upper-bound semantics for n>=1. There is no arbitrary empty-set default in the final positive-dimensional result. |
| Newton recurrence | X_0=A and X_(k+1)=(1/2)*(X_k+X_k^-1*A), for every k>=0. Prove actual unitness, the original H property and positive diagonal at each k. |
| Spectral homotopy | sI-tB is a unit for every t in the full closed interval [0,1] whenever rho(B)<s. This is a symbolic theorem, including both endpoints, not an interval numerical approximation. |
| Positive weight bridge | Original spectral M implies v=C^-1*1>0 and Cv=1. Conversely a real Z-matrix with v>0 and Cv>0 admits the original spectral sI-B witness. Neither bridge is a premise of the final theorem. |
| Shifted resolvents | Every real t>=0, including t=0. Prove both A+tI and comparison(A)+tI units and the entrywise inverse absolute-value domination. |
| Finite rational data | Any finite family including the empty family; a>0, b>0, each pole t_j>0, each weight w_j>=0. Repeated poles and zero weights are allowed. No input-dependent approximation. |
| Preserver inequalities | Expose each diagonal f(A)_ii>=f(C)_ii>0 and every off-diagonal abs(f(A)_ij)<=-f(C)_ij. Then prove the entrywise comparison inequality, a positive weight and the original spectral H conclusion. |
| Rank-one pole matrix | P=diag(0,t_j)+uu^T/b, u=(sqrt(a),sqrt(w_j)). Prove actual real positive definiteness for every valid data record, including no old poles. |
| Spectral coefficients | An actual real orthogonal Q and lambda_i>0 diagonalize P. With d=Q^T*u, prove sum_i d_i^2/lambda_i=b. New weights d_i^2/(b^2*lambda_i)>=0. No distinct eigenvalues or positive lower bound on weights is assumed. |
| Matrix reciprocal | For every original admissible A, the actual inverse product f(A)^-1*A equals the new finite ridge sum. Prove both block matrices' unitness. A scalar identity alone does not meet this contract. |
| New data and induction | One new scalar data record works for every admissible A in every dimension. Constant and linear coefficients halve. At k=1 the exact data have a=b=1/2 and no poles. For every k>=1 one valid scalar record represents that iterate for all admissible inputs. |

The only fixed numerical certificate is

`NLA.SF01.half_positive_certificate : (0 : Real) < 1 / 2`.

Implement it later using pinned LeanCert `interval_decide (trust := kernel)`. Consume the proved certificate in `initial_data_valid` and coefficient halving in `newton_data_step`; importing LeanCert without a used certificate is insufficient. There is no variable interval to subdivide. The existing IE13 exact-half certificate is an inspected syntax/dependency pattern, not evidence that this new theorem has run.

All remaining numerical assertions are symbolic. Use Mathlib's square-root and spectral theorems for arbitrary real coefficients rather than approximated eigenvalues. Do not enumerate k, expand enormous concrete block matrices, construct explicit degree-2^k polynomials, or certify finitely many sample inputs. Generic finite-index block identities and opaque proved helper boundaries keep the computation small while retaining the universal theorem.

Every exported Challenge signature is intended for Comparator. No definition holes are allowed: the Definitions module contains only explicit objects and predicates, and RidgeData has only scalar data fields. All inverse, positivity, spectral and representation claims must be proved from those explicit definitions. No proof module may import Challenge.
