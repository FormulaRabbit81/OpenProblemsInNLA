# Selected pinned API evidence

Mathlib commit: `0df444a360eaa60ab8c11dca51a86af692955474`.
Paths below are relative to its source root. Line ranges are a selected
source-reading record, not a transitive audit of Mathlib proofs. The adjacent
JSON binds literal bytes to this pin.

| Primary file and lines | Reuse in the candidate |
| --- | --- |
| `Analysis/InnerProductSpace/SingularValues.lean` 80–131 | Actual finite-support zero-extended definition; nonnegativity; zero extension; square equals Gram eigenvalue. The accepted `singular_values_semantics` supplies order and nonnegativity. |
| `Analysis/InnerProductSpace/Spectrum.lean` 275–349 | Ordered orthonormal eigenbasis and `eigenvectorBasis_apply_self_apply`, giving the diagonal-coordinate formula for every vector. |
| `Analysis/InnerProductSpace/PiL2.lean` 85–105, 151–153, 201–209 | Actual Euclidean sum inner product, squared norm, and exact domain dimension. |
| `Analysis/InnerProductSpace/PiL2.lean` 293–325, 429–458 | Basis coordinate of a basis vector is a Euclidean single, whose sole entry is one; every basis vector has norm one. |
| `Analysis/InnerProductSpace/PiL2.lean` 1235–1244 | `Matrix.toEuclideanLin` is a linear equivalence, so it is injective and preserves zero, including empty index types. |
| `Analysis/InnerProductSpace/Adjoint.lean` 581–592 | `adjoint_inner_right` identifies the Gram quadratic form with the squared image norm. |
| `Analysis/InnerProductSpace/Basic.lean` 114–116, 210–211, 389–391 | Right scalar linearity and exact inner-self/norm-square identities. |
| `Analysis/Complex/Basic.lean` 348–357 | Explicit RCLike-to-Complex cast identity, also used in the accepted GramBasis repair. |
| `Data/Complex/Basic.lean` 416–430, 662–668 | Actual real-part additive map and real-power complex-cast identity. |
| `Data/Complex/BigOperators.lean` 27–45 | `Complex.re_sum`, proved by the real-part additive homomorphism, commutes finite summation with taking real parts. |
| `Analysis/Normed/Lp/PiLp.lean` 150–177 | `single_apply` and zero entries away from the selected index. |
| `Analysis/Normed/Operator/Basic.lean` 172–238 | The actual continuous operator norm is the infimum of valid nonnegative bounds; `opNorm_le_bound` and `le_opNorm` are its upper and application bounds. |
| `Topology/Algebra/Module/FiniteDimension.lean` 306–328 | Finite-dimensional linear maps and continuous linear maps form a linear equivalence with definitionally unchanged action. |
| `Algebra/Order/GroupWithZero/Basic.lean` 705–716 | Equality and inequality of nonnegative real numbers are equivalent to equality and inequality of their squares. |

The inspected C-star matrix diagonal norm and continuous-adjoint norm
identity were alternatives, not dependencies of the chosen proof. The proof
uses no matrix norm instance and needs no prior operator-norm/SVD bridge.
