Pinned API feasibility — source inspection only

Exact source hashes and read ranges are in PINNED-API-BINDINGS.json.

| API | Role and required hypotheses |
| --- | --- |
| Matrix.PosDef.diagonal | Positive complex diagonal entries imply genuine PosDef under ComplexOrder. |
| Matrix.IsHermitian.ext | Reduce Q's Hermitian identity to star(Aji)=Aij at its actual entries. |
| Matrix.IsHermitian.posDef_iff_eigenvalues_pos | For a Hermitian finite matrix, PosDef iff every real eigenvalue is positive. |
| Matrix.IsHermitian.eigenvectorBasis and mulVec_eigenvectorBasis | Actual orthonormal eigenvectors and mulVec equation; repeated eigenvalues allowed. |
| WithLp.ofLp_eq_zero and orthonormal.ne_zero | Transport nonzeroness to the coordinate function; Spectrum.lean:235 uses this exact transport. |
| Matrix.toLin'_apply and RCLike.real_smul_eq_coe_smul | Explicitly relate the real eigenvalue action to the complex linear map. |
| Module.End.mem_eigenspace_iff and hasEigenvalue_of_hasEigenvector | Build the exact algebraic eigenvalue hypothesis from the nonzero eigenvector. |
| eigenvalue_mem_ball (global namespace) | Existing Gershgorin theorem gives the complex closed-ball row bound. |
| Complex.re_le_norm | Turn the complex distance bound into a real lower bound for λ. |
| Matrix.nonneg_iff_posSemidef and PosDef.posSemidef | Bridge actual matrix order and quadratic-form positivity. |
| CFC.sqrt_nonneg and CFC.sqrt_mul_sqrt_self | Hermitian-positive roots and exact square identity with explicit nonnegative input. |
| Matrix.PosDef.isUnit and isUnit_mul_self_iff | Invertibility of input and its identical-factor square root; no commutativity of P,Q required. |

CFC.sqrt is cfcₙ NNReal.sqrt. Its source defines a zero fallback for inputs outside the nonnegative predicate, so actual positivity must precede the square identity. The square theorem also uses semitopological-ring and Hausdorff instances. Matrix.Order imports the matrix C-star algebra and functional-calculus instances, and the frozen definitions already use MatrixOrder and Matrix.Norms.L2Operator. The future modules will explicitly use these same scopes. This establishes static API availability, not successful elaboration of unwritten proofs.
