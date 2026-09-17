# MI-13 proposed finite route, awaiting independent mathematical review

This is an informal feasibility derivation, not a Lean proof, execution report or novelty claim. It fills the external refined-commutator dependency of the canonical reduction rather than assuming the desired inequality. All inner products below are the complex Hilbert–Schmidt product `<Y,Z> = tr(Y* Z)`.

## 1. Refined commutator bound by a top eigenspace

Fix a square complex X of order r at least two and let `D(Y)=[X,Y]`. Trace cyclicity gives `D*(Y)=[X*,Y]`, so `T=D*D` is positive and self-adjoint on the r-squared-dimensional Hilbert space of all matrices. Let lambda be its greatest eigenvalue. The spectral theorem proves `||D(Y)||F^2 <= lambda ||Y||F^2` for every Y. If lambda is zero, the commutator vanishes for every Y and the target is immediate.

Suppose lambda is positive. Define the conjugate-linear map `J(Y)=[X*,Y*]`. Direct multiplication/star identities give `J^2=-T`; associativity of composition and the real coefficient minus one give `TJ=JT`. Also `||JY||F=||DY||F` and

`<Y,JY> = tr(Y* X* Y* - Y* Y* X*) = 0`

by trace cyclicity. Thus, for any nonzero top eigenvector Y, JY is a nonzero orthogonal top eigenvector (lambda is real, so conjugate linearity causes no eigenvalue change). These are two complex-linearly independent vectors. This is a concrete two-vector construction, not an assumption of eigenvalue multiplicity.

Choose an actual SVD `X=U S V*`, with U,V unitary, `S=diag(s_1,...,s_r)` and `s_1 >= s_2 >= ... >= 0`. The zero singular values must be included. On the two-dimensional top-eigenvector span, the map

`f(Z) = (U* [X,Z] V)_(1,1)`

is complex-linear. It has a nonzero kernel vector Z: if f(Y)=0 use Y; otherwise use `f(JY)Y - f(Y)JY`, which is nonzero by independence. Put `P=V* Z V` and `Q=U* Z U`. Then

`U* [X,Z] V = S P - Q S`,

and its (1,1) entry is zero. For each other pair (i,j),

`|s_i P_ij - s_j Q_ij|^2 <= (s_i^2+s_j^2)(|P_ij|^2+|Q_ij|^2)`

by two-dimensional complex Cauchy–Schwarz. Since at least one index is not one, `s_i^2+s_j^2 <= s_1^2+s_2^2`. Summing, including an upper bound by the full nonnegative P,Q sums, and using unitary Frobenius invariance yields

`lambda ||Z||F^2 = ||[X,Z]||F^2 <= 2 (s_1^2+s_2^2) ||Z||F^2`.

Cancel the strictly positive squared norm of Z. The spectral maximum bound now proves the refined inequality for every Y:

`||[X,Y]||F^2 <= 2 (s_1^2+s_2^2) ||Y||F^2`.

No interval arithmetic or perturbative invertibility argument occurs. Needed formal foundations are the Hilbert–Schmidt linear-map interface, spectral bound, actual full SVD and scalar norm inequality. If any such foundation is absent it remains a proof obligation, not a theorem premise.

## 2. Square three-factor reduction

For a unitary W, `(AWC-CWA)W=[AW,CW]`. Right multiplication by W preserves the Frobenius norm of C and the actual singular values of A, giving the canonical unitary-middle-factor bound. These invariances can be proved using the same SVD: `AW=U S (W* V)*`, so the diagonal is unchanged; this avoids treating an arbitrary chosen eigenbasis as canonically invariant.

For a square contraction B, take `B=P diag(d_i) Q*` with `0<=d_i<=1`. Put `e_i=sqrt(1-d_i^2)` and `W_plus/minus=P diag(d_i +/- i e_i) Q*`. The diagonal entries have squared modulus `d_i^2+e_i^2=1`; the two matrices are unitary and their average is B. Linearity in B and the Frobenius norm's convexity give the bound. If B is nonzero, scale it by its strictly positive operator norm; B=0 is a separate algebraic branch. No inverse of B is used, so deficient rank is retained.

## 3. Rectangular target and sharpness

For the original m-by-n A,C and n-by-m B, set r=max(m,n) and use coordinate isometries E into dimension r from m and F from n. Define Atilde=EAF*, Btilde=FBE*, Ctilde=ECF*. Exact contraction identities E*E=I and F*F=I give the original difference padded by E/F. Frobenius norms and the middle operator norm are preserved, and the first two actual singular values of Atilde equal those of A; extra eigenvalues are zero. Prove those last spectral semantics explicitly, including both orderings m<=n and n<=m and ranks zero/one. Applying the square theorem yields the exact canonical rectangular inequality with coefficient two.

The fixed two-by-two example A=diag(1,-1), B=I, C=e12 has both sides four. Its exact calculation is a useful semantic check and can prove coefficient sharpness, but it cannot substitute for the universal estimate.
