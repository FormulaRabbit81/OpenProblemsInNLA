# Exact finite boundary and scaled factorization targets, before code

PLAN ONLY for frozen IE02 contracts15 and16. Root approval must precede
implementation. Every norm below is the frozen Euclidean induced operator
norm or actual Euclidean vector norm over C. No matrix entry supremum norm,
SVD oracle, refined minimax assumption, or limiting approximation is involved.

Contract15: for every n>=1 and every n-by-n lower triangular Toeplitz U with
operatorNorm U=1, construct d<n and complex polynomials a,b satisfying all11
frozen SchurPair clauses. In particular degree(a)=d exactly, degree(b)<=d,
b(0)=1, coprimality, denominator nonvanishing on the CLOSED disk, boundary
modulus equality, finite matrix interpolation, the entire maximal kernel,
its parameter action, and finrank n-d must all survive dimension induction.
The Toeplitz symbol may have arbitrary degree; no global symbol equality is
inferred from its visible coefficients. The endpoint may occur at any stage,
including dimension1. Termination is by strictly decreasing natural dimension.

Contract16: for every n>=1 and every nonzero complex Toeplitz T, let M be its
actual operator norm. Prove M>0, normalize by the exact complex scalar
(M:C)^(-1), obtain the complete SchurPair for that normalized matrix, and
transport its parameterization to the original maximalSpace T. The action
on the same parameter vector must be precisely M times the output polynomial
vector. No parameter rescaling or change in allowed degree is permitted.
Repeated maximal singular values and the zero parameter vector remain present.

Boundary cases to be justified symbolically: n=0 is excluded solely by the
frozen hypothesis; n=1 uses the actual one-dimensional operator norm identity;
coefficient modulus1 uses the scalar endpoint; modulus<1 uses strict Schur
reduction with the exact finite inverse, including coefficient0. T!=0 is used
only to justify positive M and its inverse; no positive-definite hypothesis.

No new numerical certificate is needed: dimension recursion, scalar
normalization, algebra and norm equalities are symbolic. Retain the existing
single genuinely used kernel LeanCert descent certificate. Do not add interval
computations. This packet does not implement either contract or claim a whole
target or Comparator result.
