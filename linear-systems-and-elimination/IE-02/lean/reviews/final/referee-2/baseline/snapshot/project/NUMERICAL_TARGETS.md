# IE-02 exact numerical and semantic boundary before Lean statements

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. OpenAI Codex assistance. Preserve Tichy, Liesen, and Faber's original problem and special cases; Faber, Liesen, and Tichy's matrix-approximation background; Courtney and Sarason's interpolation background; and all reused library/code authorship. No email is included.

For every natural n >= 2, complex lambda != 0, and natural 1 <= k < n, let J be the actual upper Jordan block lambda I + N with N[i,i+1]=1. Let P_k contain ALL complex polynomials p with degree p <= k and p(0)=1. On genuine complex Euclidean coefficient space prove

    max_{norm(v)=1} min_{p in P_k} norm(p(J) v)
      = min_{p in P_k} norm_operator(p(J)).

The final theorem must include attainment of the operator minimum, attainment of the inner minimum for EVERY unit starting vector, and attainment of the outer maximum by a unit vector. It must provide a common polynomial/vector witness with norm(p*(J)v*)=norm_operator(p*(J)) and norm(q(J)v*) >= norm_operator(p*(J)) for every admissible q. Definitions of the displayed values will be actual infima/suprema of the stated norm ranges; the attainment contracts certify that these are the displayed minima/maxima. Neither side is defined by the desired equality or a chosen optimizer.

No restriction to real coefficients/vectors, divisibility, eigenvalue phase/magnitude, simple singular values, full rank, nonzero optimal residual in the affine helper, or dimension doubling is permitted. The canonical assumptions on n,k,lambda stay explicit even though the affine route is stronger. The affine theorem covers any finite list of complex lower triangular Toeplitz directions, including an empty list, dependent directions, and a zero optimal residual.

H_n is EuclideanSpace C (Fin n), not the raw function type with its sup norm. Coefficient conversion and truncation are finite sums. Every public operator norm is the norm of the actual continuous linear map on H_n. The maximal singular space is the actual kernel of T* T - norm(T)^2 I. Its full polynomial-factor description, including repeated maximal singular values, is a theorem to prove.

The finite Schur theorem must produce a numerator of exact degree d<n, a denominator of degree at most d with b(0)=1 and no zero on the closed disk, coprimeness, circle modulus equality, exact truncated interpolation, the entire maximal singular subspace, and its action. The strict branch must retain norm exactly one on the smaller block and terminate. The denominator's invertibility is proved by a finite nilpotent inverse. No CF, SVD, Schur, rank, or minimax oracle is assumed.

Weighted scalar factorization is required for every finite, possibly empty, family and arbitrary nonnegative real weights, without requiring their sum to be one. Its degree bound is preserved, with zero weights, the zero polynomial, constants, repeated roots, and circle roots included. Common circle roots are removed by degree induction; reciprocal root pairing is an equality of full multisets. Reflection always uses its explicit common degree bound. The output must preserve both the complete circle identity and its exact polynomial identity.

Subsequent compression must preserve full COMPLEX inner products, not only their real parts. The gradient image is proved compact, nonempty, and real convex. Strict real separation is converted to complex direction coefficients. Descent includes separate empty/nonempty compact-complement cases, a uniform norm decrease, and a sufficiently small positive step.

The only planned LeanCert certificate is 0 < (1/2 : R), at that single exact rational input with the smallest adequate precision, using interval_decide (trust := kernel). Its named theorem must genuinely supply the positive factor in the later step epsilon=(1/2)*min(...) used by the descent bounds. The identity 1/2+1/2=1 and all remaining inequalities are symbolic. No interval subdivision, matrix enumeration, numerical spectrum, root isolation, uniform grid, or approximate interpolation is planned. The certificate has not run.

This file precedes all new Lean statements. Definitions/Challenge will be an UNRUN proposal with intentional independent Challenge holes and no Solution. Two nonauthor statement reviews, actual root-coordinated local elaboration, and an immutable accepted freeze are required before implementation. At most one local compiler process, one thread, 4096 MiB; final real non-root Linux Comparator/default-kernel/sandbox checks remain distinct. No verification count or publication claim is made.
