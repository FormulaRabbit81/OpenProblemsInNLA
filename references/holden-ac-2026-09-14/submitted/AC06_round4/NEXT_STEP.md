# The outstanding proof obligation

For the quarter-quadratic threshold set N=n^3, r=floor(n^2/4), D=65536*N. Let H_n consist of the nonzero integer polynomials of degree at most D, with coefficients in {-1,0,1}, that vanish on every rank-at-most-r tensor. The retained proof establishes H_n is nonempty.

A sufficient next result is a deterministic polynomial-time generator of polynomially many polynomial-bit integer tensors S_(n,h), together with a proof that for each sufficiently large n there is a P_n in H_n and an h with P_n(S_(n,h)) != 0. The CRT or interpolation compactor then completes the construction; a verifier or selector for h is unnecessary.

An alternative sufficient result is a deterministic polynomially bounded integer weight vector w_n and a proof that some P_n in H_n remains nonzero under x_j=t^(w_(n,j)). Unique minimum monomials and oddness are no longer necessary; the explicit large base in Theorem 4.1 handles specialization.

Neither premise has been proved. The shifted candidate's finite Koszul certificates do not establish either one. The published coloring-count threshold cannot by itself establish a quadratic result, regardless of tensor power. A different certificate, a genuinely sharper rank threshold, or a direct proof of controlled curve/list escape is needed.

A useful falsification check for any new argument is its quantifier order: does it prove an appropriate annihilator is nonzero at the proposed list, rather than merely that an annihilator exists and that a hard tensor exists somewhere? Those two separate existence statements do not imply the required joint statement.
