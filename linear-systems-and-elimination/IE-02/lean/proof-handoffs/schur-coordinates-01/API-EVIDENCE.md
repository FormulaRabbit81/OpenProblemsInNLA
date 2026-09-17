# Coordinate and dimension reuse

Accepted plan16,20,21,24 supplies this module. Polynomial.coeff_divX and
coeff_X_mul implement finite symbol lifting; coefficient equality is extracted
from column0 only at a proved in-range row. The zero-dimensional lift is valid.
Polynomial.coeff_eq_zero_of_degree_lt supplies the final zero coordinate.
Fin.lastCases, Fin.snoc_castSucc and Fin.snoc_last prove the append/prefix
linearity. Existing schur_active_block gives norm saturation and existing
maximal_space_norm_one identifies the original kernel with norm equality.

LinearMap.restrict builds the two maps on the full maximal subspaces. Both
inverse equations are proved from M*B=B*M=1 and the actual append/prefix
identities. LinearEquiv.ofLinearMap and LinearEquiv.finrank_eq transfer
finrank without assuming simple singular values or a rank oracle.

This is a helper candidate for frozen pair-step14, not its completion.
The only imported project module is accepted SchurReduction, source matched
to actual97; all its dependency proofs are genuine uses. No compiler ran.
