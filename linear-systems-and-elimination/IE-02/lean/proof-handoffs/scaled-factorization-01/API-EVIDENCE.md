# Actual-norm scaling reuse

Accepted plan16 steps7-12 are implemented literally. euclidean_norm_attainment
supplies nonnegativity and norm-zero iff T=0; hne implies a strictly positive
real M. The complex cast is nonzero by Complex.ofReal_ne_zero. The helper
euclideanCLM_smul is proved extensionally from euclideanLin_smul_apply, then
norm_smul is applied to the actual ContinuousLinearMap normed space.
Mathlib Analysis/Normed/Operator/Basic390 and Normed/MulAction98 supply that
scalar law, Normed/Field/Basic77 gives norm_inv, and Complex/Norm106 removes
the nonnegative real cast. No ambient Matrix norm is used.

The exact frozen normalized matrix has polynomial witness (M:C)^(-1)•p via
toeplitz_smul. The full finite_schur_boundary result is retained unchanged.
The original maximalSpace kernels are identified through maximal_space_norm
and maximal_space_norm_one, using T=(M:C)•U and mul_left_cancel₀ at the
proved nonzero REAL M. The parameter polynomial, degree bound and denominator
are unchanged. The final action follows from the same scalar map identity.
Repeated maximal singular values and the zero parameter vector are retained.

The generic CLM/operator scalar helpers themselves allow dimension0; the
frozen main contract retains hn>=1. There is no new numerical certificate,
interval computation, assumption, definition change or resource override.
