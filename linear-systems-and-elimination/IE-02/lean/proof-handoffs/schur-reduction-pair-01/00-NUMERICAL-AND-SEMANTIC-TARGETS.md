# Schur strict reduction and pair-step: numerical-first targets

PLAN ONLY, before new proof sources. Await root acceptance before implementation.
Proposed modules are SchurReduction.lean and SchurPairStep.lean; both are absent.
No compiler, Lake, cache mutation, Git or network command is authorized here.

Exact frozen contract12 uses N=n+2, n>=0, U=toeplitz N p, ||U||=1,
c=p.coeff0 and ||c||<1. The symbol p is any complex polynomial. Construct a
concrete finite Toeplitz two-sided inverse B of M=I-conj(c)U, prove Z=(U-cI)B
is Toeplitz with zero diagonal, ||Z||=||activeBlock Z||=1, the precise real
squared-norm defect identity, and transport of the entire maximalSpace.

The only scalar positivity needed is alpha=1-||c||²>0. Its complex embedding
is nonzero before inversion. No inversion of c, a singular defect, a vector
of zero norm, or a polynomial value in the disk is permitted without proof.
The case c=0 remains included. A genuinely attained norm-one vector is obtained
from the existing euclidean_norm_attainment theorem, not added as a hypothesis.

Exact frozen contract14 keeps its arbitrary supplied B and both inverse
identities. From the complete smaller SchurPair at dimension n+1, prove all
11 clauses of SchurPair at dimension n+2, degree d+1, numerator c*b+X*a,
and denominator b+conj(c)*X*a. It includes disk nonvanishing, exact numerator
degree, coprimality, matrix interpolation, both directions of the full maximal
subspace parameterization, polynomial action and the stated finrank. Repeated
maximal singular values and zero polynomial parameters h are included.

Here d<n+1 implies d<=n. The common parameter degree is m=n-d, equal to both
(n+1)-1-d and (n+2)-1-(d+1). Old products a*h,b*h have degree<=n, whereas new
products have degree<=n+1. The append at the last input coordinate and prepend
at the first output coordinate are distinct. Bounds justify each zero final
coefficient; no negative integer bound is silently truncated to a natural.

All norms remain the actual Euclidean vector/operator norms and all scalars
remain complex. Only symbolic finite polynomial, matrix, inner-product and
ordered-real algebra is proposed. No sampled spectral test, interval sweep,
SVD/minimax/factorization oracle or extra LeanCert certificate is needed.
The existing single descent certificate and all 13 frozen inputs are untouched.
The final canonical n>=2, nonzero complex lam, 1<=k<n target is unchanged.
