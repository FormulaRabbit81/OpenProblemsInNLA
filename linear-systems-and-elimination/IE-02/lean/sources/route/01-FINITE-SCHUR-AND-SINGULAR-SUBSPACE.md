# Finite Schur induction at the norm boundary

This is an independently derived paper proof of the simultaneous finite contract in `00-TARGETS.md`. It is not a Lean proof or a statement-review approval. All matrices below act on the actual complex Euclidean coefficient spaces; adjoints use the inner product linear in the second argument.

The decisive simplification is to prove the interpolation pair and its entire maximal singular subspace together. There is no need to derive that subspace from an infinite-dimensional multiplication operator or to assume its dimension.

## 1. Elementary finite facts used in the induction

For `n>=1`, `H_n` consists of polynomials of degree below `n`, with the coefficient norm. Multiplication followed by truncation is represented by a lower triangular Toeplitz matrix. Thus the Toeplitz algebra is the image of `C[X]/(X^n)` under `X -> S_n`, where `S_n` is the lower shift. It is commutative, and `S_n^n=0`. A strictly lower triangular Toeplitz matrix is a polynomial in `S_n` with zero constant term, so its `n`th power is zero.

If a Toeplitz matrix has nonzero constant diagonal `alpha`, write it as `alpha I+K`, with `K^n=0`. Its inverse is the finite Toeplitz polynomial

`alpha^(-1) sum_{j=0}^{n-1} (-alpha^(-1) K)^j`.

Multiplying out the finite geometric sum proves both inverse identities. This is a finite algebraic inverse, without any convergence or spectral hypothesis.

The actual operator norm of a map on `H_n` is attained on the unit sphere: the sphere is nonempty and compact, and `x -> ||U x||` is continuous. If its maximum is `M`, rescaling each nonzero vector proves `||U x||<=M||x||`, so the operator-norm upper bound gives `||U||<=M`; the reverse inequality is the operator-norm evaluation bound. This uses no singular-value decomposition.

For a contraction `U`, let `D_U=I-U*U`. It is self-adjoint and its quadratic form is

`q_U(x)=<x,D_U x>=||x||^2-||Ux||^2>=0`.

For completeness, a self-adjoint positive quadratic form satisfies `q(x)=0 iff D x=0`. The reverse implication is immediate. For the forward implication put `A=||D x||^2` and `B=q(Dx)>=0`. Positivity at `x+s Dx` gives `0<=2s A+s^2 B` for every real `s`. If `A>0`, choosing `s=-A/(B+1)` makes the right side `-A^2(B+2)/(B+1)^2<0`, a contradiction. Hence `A=0` and `Dx=0`. In particular

`E_U := ker(I-U*U) = {x : ||Ux||=||x||}`.

The zero vector is included. The same argument works for `t^2 I-T*T`, with `t=||T||`.

## 2. Boundary-preserving Schur reduction

Let `||U||=1`, and let `c` be its constant diagonal. The first column evaluated on the first standard unit vector gives `|c|<=1`.

If `|c|=1`, the same column estimate says

`1 >= ||U e_0||^2 = 1 + sum_{j=1}^{n-1} |u_j|^2`.

Every summand vanishes, and Toeplitz structure gives `U=c I`. Take `d=0`, `a=c`, and `b=1`. All interpolation, disk, degree, coprimality, action, and singular-subspace claims follow immediately: `E_U=H_n`.

Suppose instead `|c|<1`. Set the positive real number `alpha=1-|c|^2`, and define

`M=I-conj(c) U`,

`Z=(U-c I) M^(-1)`.

The constant diagonal of `M` is `alpha`, so its inverse exists by the finite nilpotent formula above. Both `M^(-1)` and `Z` are Toeplitz, and `Z` is strictly lower triangular. Direct multiplication, with no commutation of adjoints presumed, gives

`M* M-(U-c I)*(U-c I)=alpha (I-U*U)`,

and therefore

`I-Z*Z=alpha M^{-*}(I-U*U)M^(-1)`.                         (S1)

An equally useful scalar form, for every `x`, is

`||M x||^2-||Z M x||^2=alpha (||x||^2-||U x||^2)`.          (S2)

Here `M^{-*}` means `(M^(-1))*`. The cross terms in (S2) agree because

`Re(conj(c)<x,Ux>)=Re(c<Ux,x>)`.

Since `M` is onto and the right side of (S2) is nonnegative, `Z` is a contraction. Formula (S2), or the invertible congruence (S1), also proves

`x in E_U iff Mx in E_Z`.                                 (S3)

For `n=1` the strict branch cannot occur: a scalar operator of norm one has `|c|=1`. Hence this branch has `n>=2`.

Write a vector of `H_n` as `(g,eta)`, where `g` contains the first `n-1` coefficients. A strictly lower triangular Toeplitz `Z` has the exact action

`Z(g,eta)=(0,Vg)`,                                        (S4)

where `V` is the `(n-1)`-dimensional Toeplitz matrix whose symbol is the symbol of `Z` divided by `X`. The leading zero in the output is a different coordinate decomposition from the trailing `eta` in the input; equation (S4) is the explicit coordinate statement.

Consequently `||Z||=||V||` and

`E_Z = { (g,0) : g in E_V }`,                             (S5)

provided `V` is a contraction. Indeed, for every `(g,eta)`, the norm defect is

`||g||^2-||Vg||^2+|eta|^2`,

the sum of two nonnegative terms. The upper bound `||V||<=1` follows by applying `Z` to `(g,0)`.

It remains essential to prove that `||V||=1`, rather than merely `<=1`. Choose a unit `x` with `||Ux||=1` by finite-dimensional norm attainment. The vector `y=Mx` is nonzero and satisfies equality in (S2). Writing `y=(g,eta)`, equation (S5) yields `eta=0` and `||Vg||=||g||`. Since `y!=0`, also `g!=0`. The operator norm bound and normalization of `g` now give `||V||>=1`. Therefore `||V||=1`, and induction applies to the smaller dimension.

This is the singular-endpoint argument. It does not perturb the norm, take a limit of strict contractions, assume invertibility of `I-U*U`, or assume a maximal-singular-value multiplicity.

## 3. Reconstruct the polynomial pair

By induction for `V`, choose `d_1,a_1,b_1` with

`d_1<=n-2`, `degree(a_1)=d_1`, `degree(b_1)<=d_1`, `b_1(0)=1`,

and all the disk, coprimality, interpolation, action, and subspace conclusions. Define

`d=d_1+1`,

`a=c b_1+X a_1`,

`b=b_1+conj(c) X a_1`.                                   (S6)

Then `degree(a)=d`: the term `X a_1` has degree `d_1+1`, strictly above the possible degree of `c b_1`, so its leading coefficient cannot cancel. Also `degree(b)<=d`, `b(0)=1`, and `d<=n-1`.

The two exact polynomial identities

`b-conj(c) a=alpha b_1`,

`a-c b=alpha X a_1`                                      (S7)

prove coprimality. Indeed `a_1,b_1` are coprime and `b_1(0)=1` makes `X,b_1` coprime. Thus `X a_1,b_1` are coprime. An explicit Bézout derivation is available: if `u a_1+v b_1=1` and `b_1=1+X q`, then

`1=b_1(u a_1+v b_1-v X q)-u q X a_1`.

Substitute (S7) and divide by `alpha!=0` to express `1` as a polynomial linear combination of `a,b`. No root argument is needed for this step.

For any `|z|<=1`, induction gives `b_1(z)!=0` and

`|z a_1(z)|<=|b_1(z)|`.

If `b(z)=0`, then

`|b_1(z)|=|c| |z a_1(z)|<=|c| |b_1(z)|<|b_1(z)|`,

which is impossible. Thus the new denominator is nonzero on the entire closed disk. A direct complex norm-square expansion gives

`|b(z)|^2-|a(z)|^2=alpha (|b_1(z)|^2-|z a_1(z)|^2)>=0`.   (S8)

On `|z|=1`, the final difference vanishes by induction, so equality holds. This handles `c=0` as well: then `a=X a_1` and `b=b_1`.

## 4. Interpolation and the entire singular subspace

Work first inside the finite Toeplitz algebra. By the smaller-dimensional interpolation identity and the explicit shifted block in (S4),

`Z b_1(S_n)=S_n a_1(S_n)`.                               (S9)

To verify (S9) coefficientwise, the symbol of `Z` is `X` times the symbol of `V`, and equality modulo `X^(n-1)` becomes equality modulo `X^n` after multiplication by `X`. No coefficient of order `n` or higher can enter.

Multiply (S9) by `M`. All unstarred Toeplitz factors commute and `ZM=U-cI`. Rearrangement gives

`U (b_1(S_n)+conj(c) S_n a_1(S_n))=c b_1(S_n)+S_n a_1(S_n)`,

hence

`U b(S_n)=a(S_n)`.                                      (S10)

Because `b(0)=1`, its Toeplitz evaluation is invertible; (S10) uniquely specifies the first `n` coefficients of `a/b`. Also (S7) and (S10) give

`M b(S_n)=alpha b_1(S_n)`.                               (S11)

Set `m=n-1-d=n-2-d_1>=0`. If `degree(h)<=m`, then

`degree(bh)<=n-1`, `degree(ah)<=n-1`, `degree(b_1h)<=n-2`.

Thus none of these products is truncated when read as a vector in the indicated space. Equations (S10)-(S11) become the actual vector identities

`U(bh)=ah`, `M(bh)=alpha b_1h`.                           (S12)

Induction says `E_V={b_1h : degree(h)<=m}`. Combining (S3), (S5), and (S12) proves both inclusions:

* If `x in E_U`, then `Mx=b_1h` for such an `h`. Since `M` is injective, `x=b(alpha^(-1)h)`, and the scalar multiple has the same degree bound.
* If `x=bh` with the degree bound, then `Mx=alpha b_1h` lies in the embedded `E_V`, hence in `E_Z`; (S3) gives `x in E_U`.

Therefore

`ker(I-U*U)={bh : degree(h)<=n-1-d}`,

and `U(bh)=ah` on that entire subspace. Zero polynomials have been included throughout. This closes the simultaneous induction. In particular multiplication by the nonzero polynomial `b` identifies this subspace with `H_(n-d)`, so its complex dimension is exactly `n-d`. This dimension is a conclusion, never a rank assumption; every possible repeated maximal singular value is covered.

There are at most `n-1` strict Schur steps, since each reduces the dimension by one and dimension one must take the scalar endpoint. The reconstruction degree is exactly the number of strict steps. There is no unproved termination or unit-modulus endpoint assumption.

For nonzero `T`, use `t=||T||>0` and `U=T/t`. The same pair satisfies `T(bh)=t ah` and

`ker(T*T-t^2 I)={bh : degree(h)<=n-1-d}`.

## 5. Recover the classical finite Blaschke formulation if required

The minimal final IE-02 implementation can consume (S10) and the proved subspace/action identities directly. Nevertheless they give the exact classical CF interpolation form, without assuming CF.

For a polynomial of degree at most `r`, define the fixed-degree conjugate reflection `p#_r(z)=sum_{j=0}^r conj(p_j) z^(r-j)`. It obeys `p#_r(z)=z^r conj(p(z))` on the unit circle, and `(p q)#_(r+s)=p#_r q#_s`. Two polynomials equal on the entire circle are equal as polynomials; an elementary infinitude proof and the full reflection identities appear in `02-WEIGHTED-FACTORIZATION.md`.

From `|a|=|b|` on the circle, obtain `a a#_d=b b#_d`. Coprimality of `a,b` implies `a` divides `b#_d`. Since `b(0)=1`, the latter polynomial has degree exactly `d`. Thus `b#_d=kappa a` for a nonzero constant `kappa`, and reflecting again gives `b=conj(kappa) a#_d`.

Every root of `a` lies strictly inside the disk: a root `alpha` outside or on the circle would be nonzero, and the reflection evaluation identity would make `1/conj(alpha)` a root of `a#_d`, hence of `b`, in the closed disk. This contradicts denominator nonvanishing.

The fundamental theorem of algebra factors `a=gamma product_{j=1}^d (X-alpha_j)`, with multiplicities and `|alpha_j|<1`. Reflecting and using `b(0)=1` gives exactly

`b=product_{j=1}^d (1-conj(alpha_j)X)`.

For `|z|=1`, each `|z-alpha_j|=|1-conj(alpha_j)z|`; the factors are nonzero there. Hence `|a|=|b|` forces `|gamma|=1`. The empty product covers `d=0`.

Finally let `B=a/b`. For each `alpha_j`, the geometric polynomial

`g_(j,L)(z)=sum_{r=0}^L (conj(alpha_j)z)^r`

converges uniformly on the unit circle to `(1-conj(alpha_j)z)^(-1)`: its error is at most `|alpha_j|^(L+1)/(1-|alpha_j|)`. Finite products therefore give polynomial approximations `G_L=product_j g_(j,L)` converging uniformly to `1/b`. For `L>=n-1`, the finite identity

`b G_L=product_j (1-(conj(alpha_j)X)^(L+1))`

is `1` modulo `X^n`. It follows that the first `n` coefficients of `a f G_L` are exactly `U f`, by (S10), for every `f in H_n`. On polynomials the normalized-circle orthogonal projection is coefficient truncation, by the elementary monomial orthogonality identities. Uniform convergence implies circle `L^2` convergence, and that finite orthogonal projection is continuous. Passing to the limit proves

`Pi_n(Bf)=Uf`, and consequently `T f=t Pi_n(Bf)`.

This last paragraph supplies the analytic compression statement as a proved paper corollary. It need not be implemented to complete the finite algebraic route to IE-02. If it is put into a Lean theorem, its geometric-series/projection bridge must also be formalized and reviewed; it cannot be silently treated as a pre-existing library result.
