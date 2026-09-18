# From the foundations to the full IE-02 target

This paper route consumes the unconditional finite results proved in `01-FINITE-SCHUR-AND-SINGULAR-SUBSPACE.md` and `02-WEIGHTED-FACTORIZATION.md`. It proves the same affine Toeplitz minimax statement as the manuscript, using exact polynomial coefficients and direct convexity of the gradient image. It introduces no CF, SVD, minimax, rank, or factorization hypothesis. No part has been Lean-compiled in this packet.

## 1. Preserve the Euclidean norm and full complex forms algebraically

For `degree(u)<=N` and any polynomial `v`, coefficient multiplication gives

`[X^N](u#_N v)=sum_{i=0}^N conj(u_i) v_i`

`                 =<u,tau_(N+1)(v)>`.                   (C1)

In particular, `[X^N](u#_N u)=||u||_2^2`, understood as a real number embedded in `C`. Terms of `v` above degree `N` cannot contribute to that coefficient. This is the exact coefficient inner product, not a norm on raw function types with their default supremum norm.

Let `T!=0` be lower triangular Toeplitz of size `n>=1`, put `t=||T||>0`, and take the pair `a,b,d` from the simultaneous Schur theorem. Write `N=n-1` and `m=N-d`. Let `R_j` be any finite family of lower triangular Toeplitz directions with symbols `r_j`. Suppose unit vectors `f_nu` in `E=ker(T*T-t^2 I)` have nonnegative real weights `w_nu` summing to one.

By the proved subspace formula, write `f_nu=b h_nu`, with `degree(h_nu)<=m`. Weighted factorization gives `h` with the same degree bound and polynomial identity

`h#_m h=sum_nu w_nu (h_nu)#_m h_nu`.                    (C2)

Set `f=bh`. Then `f in E` and `Tf=t ah`. By fixed-degree multiplicativity of reflection,

`(bh)#_N=b#_d h#_m`, and `(ah)#_N=a#_d h#_m`.

Equation (C1) yields

`||bh||^2=[X^N]((b#_d b)(h#_m h))`,                     (C3)

`<T(bh),R_j(bh)>=t [X^N]((a#_d r_j b)(h#_m h))`.        (C4)

Substitute (C2) into (C3)-(C4) and use coefficient linearity. It follows that `||f||^2=sum_nu w_nu||f_nu||^2=1`, hence `||f||=1`, and simultaneously

`<Tf,R_j f>=sum_nu w_nu <Tf_nu,R_j f_nu>`.

The last equality is in `C`, so both real and imaginary parts are preserved. There is no integration, interchange of limits, loss of truncation terms, or restriction to one real quadratic form. The cases `d=0`, `m=0`, repeated maximal singular values, and zero individual weights all remain included.

## 2. The gradient image is itself compact and convex

Define

`G={ (<Tf,R_1 f>,...,<Tf,R_k f>) : f in E, ||f||=1 }`

as a subset of `C^k`, regarded as a real finite-dimensional vector space. It is nonempty by operator-norm attainment and the kernel/equality lemma. It is compact because `E` is a closed linear kernel and the unit sphere is compact; the gradient map is continuous.

Taking just two vectors with weights `rho` and `1-rho`, for `0<=rho<=1`, in section 1 proves that `G` is convex over the reals. Therefore it is already a closed convex set. The next separation argument can act on `G` directly. This removes the otherwise separate need to prove that a compact set has compact convex hull and to extract a finite convex combination. It does not weaken the target or assume convexity: the scalar factorization establishes convexity.

## 3. Complete separation contradiction, including an empty complement

Suppose `T` minimizes the operator norm in `T+span_C{R_1,...,R_k}`. Assume for contradiction that `0` is not in `G`. Strict real separation of a point from a closed convex set supplies a real continuous linear functional `ell` and `gamma>0` such that

`ell(g)>=gamma` for every `g in G`.

Every real linear functional on `C^k` has the form

`ell(z)=Re(sum_j c_j z_j)`.

Explicitly `c_j=ell(e_j)-i ell(i e_j)`; this formula shows that no complex-linear separation assumption is being made. Set `D=sum_j c_j R_j` and `q(f)=Re<Tf,Df>`. The separation inequality is

`q(f)>=gamma` for every unit `f in E`.

On the full unit sphere define the relatively open set `U={f:q(f)>gamma/2}` and its closed complement `K={f:q(f)<=gamma/2}`. All maximal singular unit vectors lie in `U`.

If `K` is nonempty, compactness gives an attained maximum `s` of `||Tf||^2` on `K`. This maximum is strictly below `t^2`: equality would put an attaining unit vector in `E` by the already proved kernel/equality lemma, contradicting membership in `K`. Thus `beta=t^2-s>0`, and `||Tf||^2<=t^2-beta` on `K`.

Put `L=||D||^2` and `C=2t||D||+L`. Choose a real `epsilon>0` satisfying

`epsilon<=1`, `epsilon<=gamma/(2(L+1))`,

and, when `K` is nonempty, `epsilon<=beta/(2(C+1))`.

For example, half the minimum of the displayed positive bounds works. When `K` is empty, omit its bound entirely; no maximum over an empty set and no invented spectral gap is used.

For a unit vector the exact expansion is

`||(T-epsilon D)f||^2=||Tf||^2-2epsilon q(f)+epsilon^2||Df||^2`.

On `U` it is at most `t^2-epsilon gamma/2<t^2`. On nonempty `K`, use `|q(f)|<=t||D||`, `epsilon<=1`, and its bound for `epsilon` to obtain

`||(T-epsilon D)f||^2<=t^2-beta+epsilon C<=t^2-beta/2<t^2`.

These are uniform estimates on the two sets. The norm of `T-epsilon D` is attained at a unit vector; applying the relevant estimate there gives `||T-epsilon D||<t`. But `-epsilon D` belongs to the allowed complex linear direction space, contradicting minimality. Hence `0 in G`.

By the definition of `G`, there is a unit vector `f in E` with every full complex equation `<Tf,R_j f>=0`. No differentiability of the largest singular value, uniqueness, or simplicity assumption was used. If there are zero directions (`k=0`), the image space has only its zero vector and the same conclusion is immediate.

## 4. Affine Toeplitz minimax with all extrema attained

Let `Y,R_1,...,R_k` be lower triangular Toeplitz matrices of common size `n>=1`, and `X=span_C{R_1,...,R_k}`. The affine set `A=Y-X` is nonempty and closed in a finite-dimensional normed matrix space using the actual induced Euclidean operator norm.

Its minimum distance from zero is attained. One explicit proof is to intersect `A` with the closed ball of radius `||Y||`. This intersection contains `Y` and is compact, so the continuous norm has a minimum there. Every point of `A` outside that ball has strictly larger norm than `||Y||`, hence cannot improve the found minimum. Write the minimizer as `T=Y-X_*` and its norm as `t`.

For every fixed unit vector `f`, the image subspace `{X f:X in X}` is a finite-dimensional linear subspace of `C^n`, hence closed. Its distance from `Yf` is attained by the same compact-ball argument, or by orthogonal projection. Taking a preimage in `X` of an attaining vector proves that the inner minimum over `X` exists, with no injectivity or full-rank condition on the parameterization.

If `T=0`, choose any unit vector. Both the inner minima and the operator-norm minimum are zero, attained at `X_*`, so the affine minimax equality follows.

Suppose `T!=0`. Apply section 3 to the minimizer; `T+X=Y-X` because `X` is a linear space. It produces a unit `f` with `||Tf||=t` and `<Tf,R_j f>=0` for every direction. By complex linearity in the second slot, `<Tf,(X_*-X)f>=0` for every `X in X`. Thus exact Pythagoras gives

`||(Y-X)f||^2=||Tf+(X_*-X)f||^2`

`                 =t^2+||(X_*-X)f||^2>=t^2`.

Taking `X=X_*` attains `t`. Conversely, for every unit vector `g`, its inner minimum is at most `||(Y-X_*)g||<=t`. Therefore the maximum over unit vectors exists and is attained at the constructed `f`, and

`max_{||f||=1} min_{X in X} ||(Y-X)f|| = min_{X in X} ||Y-X||`.

This proves the complete affine Toeplitz statement without assuming a general minimax theorem.

## 5. Exact original Jordan-block interface

Let `n>=2`, `lambda in C` with `lambda!=0`, and `1<=k<n`. Let `W` be coordinate reversal. It is a complex linear isometry with `W*=W` and `W^2=I`. Direct entry calculation gives

`A=W J_n(lambda) W*=lambda I+S_n`.

All powers of `A` are lower triangular Toeplitz. Apply section 4 with `Y=I` and `X=span_C{A,A^2,...,A^k}`. Its residual matrices are exactly `p(A)` for all complex polynomials of degree at most `k` with `p(0)=1`: expand `p=1+sum_{j=1}^k p_j X^j` in one direction, and choose `p=1-sum_{j=1}^k c_j X^j` for a spanning representation of the matrix direction in the other.

Polynomial evaluation commutes with the reversal conjugation, and `W` maps the whole unit sphere bijectively to itself. The Euclidean operator norm is unchanged under these isometries. Transporting the attained affine equality therefore proves exactly

`max_{||v||_2=1} min_{p in P_k} ||p(J_n(lambda))v||_2`

`             = min_{p in P_k} ||p(J_n(lambda))||_2`.

The polynomial and vector witnesses described in `00-TARGETS.md` follow from the attaining `X_*` and `f`. The construction retains all complex coefficients and vectors, all `n>=2`, all `1<=k<n`, every nonzero complex `lambda`, and every maximal singular multiplicity.

The proof is actually insensitive to the phase or magnitude of `lambda`, but the final canonical statement should retain the original assumptions. One may additionally prove strict positivity for `k<n`: `p(A)=0` would force every coefficient of `p(lambda+X)` below degree `n` to vanish by the independent lower-shift powers; since its degree is below `n`, that polynomial is zero, hence so is `p`, contradicting `p(0)=1`. This extra positivity is not needed for the affine theorem or for handling its zero-residual branch.

## Status and remaining formal work

At paper level, the Schur boundary reduction, its exact subspace pullback, the weighted factorization, preservation of every complex form, direct gradient-image convexity, separation estimates, extrema, and final Jordan interface are now supplied as a complete finite route. This is an independent derivation from the source target, not a claim that another reviewer has accepted the new route.

The substantial remaining task is formal implementation and independent statement/proof review. Exact finite Toeplitz algebra/coordinate bridges, Schur defect identities, fixed-degree reflection helpers, reciprocal-root multiset arguments, and the coefficient-preservation interface are not located as ready-made theorems in the pinned sources. They must be proved. The actual Lean run and final non-root Linux Comparator/kernel/sandbox run also remain completely unrun for IE-02.
