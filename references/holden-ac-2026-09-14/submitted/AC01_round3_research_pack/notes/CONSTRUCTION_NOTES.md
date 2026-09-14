# Construction notes

## What changed in this round

The preceding round retained coordinate-isotropic graph tensors. This round instead uses the three slice matrices of the six-permutation tensor P as a non-coordinate isotropic space for B_1 tensor B_2. Two nondegenerate rational 3-by-3 forms make all nine pairings of those slices vanish.

After adding one padding coordinate, the forms are rationally split. Tensoring their three-dimensional cores with odd-dimensional split forms gives residual sizes t = 3 ell + 1. The retained head-large rows use inverse-form duals; the retained large-large rows are sums of two coordinates. Their trilinear coefficients are exactly P tensor Z_(ell_1,ell_2).

This exact P factor explains the term 3 rho (ell_1 ell_2)^(2/3) in the scalar lower estimate. It is not obtained by multiplying two unrelated entropy bounds or by assuming a stronger lower bound on Z.

## Active dimension is not actual dimension

The first improved squaring stage has 40,401 actual main coordinates but active dimension 39,963. Rows involving an old head can fall into already-counted subspaces modulo the contraction radical. They are nevertheless retained as independent coordinates of the actual limiting tensor. The complement calculation uses active dimensions only; the tensor calculation uses actual rows.

## Rational complement construction

The report gives an explicit reflection algorithm in a paired basis. A nonzero isotropic vector w can be mapped to a paired coordinate e by reflection in w-e, whose norm is nonzero when the pairing of w and e is nonzero. Repeating this operation splits off the chosen isotropic space and its dual, leaving the required hyperbolic complement. No unverified square-root extension is needed.

## Reproducibility boundaries

The certificate contains a complete small degeneration and the numerical endpoint enclosures. Literal lifted restrictions are generated and checked for six sizes, including the first bound stage's ell = 37. Subsequent enormous maps are covered by the all-size algebraic construction, not stored dense matrices. This distinction is stated in the report and the verifier output.
