# IE-02 foundation preflight: exact targets before implementation

Prepared on 16 September 2026 by agent `/root/ie02_foundation_preflight` as an independent mathematical preflight. This is prose mathematics and source inspection only: no Lean implementation, compiler run, Comparator run, Git mutation, publication, or verification-count claim. This file was written before the proof-route files. The canonical mathematical author is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Prior authorship and licenses remain applicable to any later reused code.

The source packet is `/tmp/nla-lean-next-20260915/next-statements/interval-elimination-next-triage`, whose complete `REPORT.md`, IE-02 part of `OBLIGATIONS.md`, `sources/IE-02-README.md`, and complete `sources/IE-02.tex` were read. The source packet binds the canonical sources to upstream commit `d348d7471e2ff881ae30fb8a9c40323a61cd383a`. Exact new read scopes and byte hashes are recorded separately.

## Complete original target

For every integer `n >= 2`, every complex `lambda != 0`, and every integer `1 <= k < n`, let `J = lambda I + N`, where `N[i,j] = 1` exactly when `j = i+1`. On the actual Euclidean space `C^n`, with its induced operator norm, and with

`P_k = { p in C[X] : degree(p) <= k and p(0)=1 }`,

prove

`max_{||v||_2=1} min_{p in P_k} ||p(J)v||_2 = min_{p in P_k} ||p(J)||_2`.

All coefficients and all vectors are complex. Every extremum must have an attainment proof; an infimum/supremum over a totalized empty set does not express this target. A sufficient witness is `p_* in P_k`, `||v_*||=1`, with `p_*` operator-norm minimal, `||p_*(J)v_*||=||p_*(J)||`, and `||p(J)v_*|| >= ||p_*(J)||` for every `p in P_k`. The inner minimum must also exist for every unit vector.

The more general affine Toeplitz minimax theorem in the manuscript remains the proposed route. The zero optimal residual is permitted there and is handled separately. No eigenvalue regime, divisibility, rank, simple singular value, real-coefficient, dimension-doubling, CF, SVD, minimax, or spectral-factorization oracle may enter as an extra final hypothesis.

## Finite conventions

`H_n` means polynomials of degree strictly below `n`, equivalently coefficient vectors indexed by `0,...,n-1`. It has inner product `sum_i conj(f_i) g_i`, linear in the second argument, and the Euclidean coefficient norm. Write `tau_n` for coefficient truncation below `n`, and `S_n f = tau_n(X f)`. A lower triangular Toeplitz matrix is exactly `r(S_n)`, and acts by `tau_n(r f)`. Polynomial degree statements include zero by using the ordinary extended degree, or by an explicit `p=0 or natDegree(p)<=bound` convention. No negative natural-number bound is silently truncated.

For `n >= 1` and `U` lower triangular Toeplitz of actual operator norm one, the finite foundation to prove is the existence of `d,a,b` with:

1. `0 <= d <= n-1`, `degree(a)=d`, `degree(b)<=d`, `b(0)=1`, and `a,b` coprime.
2. `b(z)!=0` on the closed unit disk; `|a(z)|<=|b(z)|` there; `|a(z)|=|b(z)|` on its boundary.
3. `U b(S_n) = a(S_n)`. Equivalently, the first `n` formal Taylor coefficients of `a/b` are the Toeplitz symbol of `U`; its denominator is a unit in `C[X]/(X^n)`.
4. `ker(I-U*U) = { b h : degree(h)<=n-1-d }`, under coefficient identification, with the zero polynomial included.
5. `U(b h) = a h` for every such `h`.

For nonzero `T`, set `t=||T||>0` and `U=T/t`. This gives `ker(T*T-t^2 I)={b h}` and `T(b h)=t a h`. If the analytic compression version is desired, (3) plus denominator nonvanishing gives `T f=t Pi_n((a/b)f)`; the final minimax route can instead consume (4)-(5) and polynomial circle identities, avoiding an unnecessary Hardy-space implementation.

## Degree-preserving scalar factorization target

For every natural `m`, every finite (possibly empty) family `h_j in C[X]` of degree at most `m`, and arbitrary real weights `w_j>=0`, produce `h in C[X]` of degree at most `m` such that

`|h(z)|^2 = sum_j w_j |h_j(z)|^2` for every complex `z` with `|z|=1`.

No weight-sum normalization is needed for this lemma. Zero weights, all-zero families, the zero polynomial, constants, repeated roots, and unit-circle roots are included. The factorization must be an identity on the entire circle, not a finite-grid test.

## Numerical and computational obligations

The proof is symbolic and uniform in all dimensions and coefficients. There is no numerical eigensolver, interval sweep, numerical CF oracle, or root-isolation oracle. The essential inequalities are consequences of hypotheses: `1-|c|^2>0` in the strict Schur branch; real square roots of nonnegative weights; and positivity of the scaling constant in the strict spectral factorization branch. These are exact ordered-field/complex norm deductions, not standalone numerical approximations requiring a LeanCert interval certificate.

The final separation contradiction can use a single symbolic sufficiently-small positive epsilon; an explicit choice and proof are supplied in the route file. This preflight performs no numeric sampling. Every eventual claim about local Lean, kernel-mode LeanCert, or Linux Comparator checks remains outstanding until actually run, and must be reported with exact commands, hashes, logs, and reviewer scope.
