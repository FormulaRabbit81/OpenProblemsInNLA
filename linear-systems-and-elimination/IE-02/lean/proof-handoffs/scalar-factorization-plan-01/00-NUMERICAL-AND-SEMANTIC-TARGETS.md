# Exact scalar-factorization targets, before implementation

PLAN ONLY for frozen IE02 contracts27 and28. The accepted original finite
paper route is foundation-preflight/02-WEIGHTED-FACTORIZATION.md. All complex
polynomial coefficients, arbitrary natural m and family size l, actual complex
moduli and the frozen fixed-bound conjugate reflection are retained.

Strict27: given degree(q_j)<=m and no common root at ANY point of the complex
unit circle, construct h of degree<=m with |h(z)|^2=sum_j|q_j(z)|^2 on the
ENTIRE circle. No real coefficient, simple root, m>=1, l>=1, factor oracle,
normalization of the sum or numerical grid hypothesis may be added. If ell=0
in the effective polynomial, the result is still required. Its positivity
comes from the given family, not from an assumption that a complex multiplier
is real.

Weighted28: for arbitrary nonnegative real weights w_j, construct degree(h)<=m
with the exact weighted norm equality on the entire circle AND the polynomial
identity h*conjReflect m h=sum_j C(w_j:C)*(q_j*conjReflect m q_j).
Zero weights, empty families, all-zero polynomials, constants, m=0, repeated
circle roots and a degree strictly below m must remain valid. Weights need
not sum to1. The same fixed m is used for every reflection in the final
polynomial equality. Do not substitute actual natDegree for this bound.

Exact scalar quantities: Q(z)=sumSquares q z; P=effectivePolynomial m ell q;
h0=rootProduct(insideRoots P); R=|h0(1)|^2; beta=Q(1)/R. In the strict branch,
prove Q(1)>0, R>0, kappa=(beta:C) and beta>0 before using real sqrt(beta).
No square root of a general complex multiplier is chosen. All powers canceled
on the circle have proved nonzero base z. In the common-root branch, never
cancel z-zeta; both sides vanish when z=zeta.

Implementation is not authorized by this packet. Exact prerequisite26 is
being authored independently; it must actually pass before dependent proof
implementation, alongside root plan acceptance. No new interval computation,
numerical eigensolver, root-isolation calculation or extra LeanCert certificate
is needed. Retain the existing minimal kernel descent certificate.
