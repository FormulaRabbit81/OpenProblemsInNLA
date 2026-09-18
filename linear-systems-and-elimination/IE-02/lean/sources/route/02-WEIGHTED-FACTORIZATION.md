# A finite degree-preserving weighted scalar factorization

This independently derived paper proof covers the exact target in `00-TARGETS.md`. It removes common circle factors before reciprocal-root pairing, so it does not assume or invoke the real-analytic even-multiplicity assertion in the manuscript. The factorization is not implemented in Lean here.

## 1. Algebraic preliminaries

For `degree(p)<=r`, define

`p#_r = sum_{j=0}^r conj(p_j) X^(r-j)`.

The zero polynomial is allowed, and `r` is an explicit degree bound rather than necessarily the actual degree. Coefficient comparison proves:

* `(p#_r)#_r=p` and `degree(p#_r)<=r`.
* `(p+q)#_r=p#_r+q#_r`, and `(c p)#_r=conj(c) p#_r`.
* `(p q)#_(r+s)=p#_r q#_s` whenever `degree(p)<=r` and `degree(q)<=s`.
* For `z!=0`, `p#_r(z)=z^r conj(p(1/conj(z)))`; on `|z|=1` this is `z^r conj(p(z))`.
* The coefficient of `X^r` in `p#_r` is `conj(p(0))`. Thus if `p(0)!=0`, this reflection has degree exactly `r`.

These are fixed-degree reflection statements. Replacing `#_r` indiscriminately by reflection at `natDegree(p)` is incorrect when leading coefficients vanish or when products use a common degree bound.

The unit circle is infinite without using complex analysis. For real `t`, the Cayley expression `(1+i t)/(1-i t)` is defined, has modulus one, and is injective in `t`: equality of two such fractions, after multiplying their nonzero denominators, gives `2i(t-s)=0`. Since a nonzero polynomial has only finitely many roots, two polynomials agreeing on the entire unit circle are identical. This justifies every later passage from a circle identity to a polynomial identity.

## 2. Fold the weights into a finite family

For the given nonnegative weights put `q_j=sqrt(w_j) h_j`, with the nonnegative real square root embedded in `C`. Then `degree(q_j)<=m` and

`sum_j |q_j(z)|^2=sum_j w_j |h_j(z)|^2`.

It suffices to factor the unweighted sum for an arbitrary finite family `q_j`. Zero weights give `q_j=0` automatically and impose no root condition on a discarded summand. An empty family is included.

Prove the unweighted assertion by induction on the natural degree bound `m`.

If every `q_j=0`, choose the zero polynomial `h=0`. This settles the empty-family and identically-zero cases, including `m=0`.

Now suppose some `q_j` is nonzero.

## 3. Common circle-root removal is a terminating branch

Suppose there exists `zeta` with `|zeta|=1` and `q_j(zeta)=0` for every index `j`. The factor theorem gives

`q_j=(X-zeta) r_j` for every `j`.

When `q_j=0`, take `r_j=0`. For a nonzero `q_j`, its quotient is nonzero and `degree(r_j)=degree(q_j)-1`. In particular `m>=1`, because a nonzero constant cannot vanish at `zeta`, and every `r_j` has degree at most `m-1`.

Apply the induction hypothesis to `r_j`, obtaining `r` of degree at most `m-1` with `|r(z)|^2=sum_j |r_j(z)|^2` on the circle. Set `h=(X-zeta)r`. Then `degree(h)<=m`, including the case `r=0`, and for every point of the circle, including `z=zeta`,

`|h(z)|^2=|z-zeta|^2 sum_j |r_j(z)|^2=sum_j |q_j(z)|^2`.

No cancellation or division by `z-zeta` is performed on the circle. Every visit to this branch lowers the degree bound by one, so induction terminates after at most the original `m` steps. Repeated unit-circle roots are removed as many times as necessary; no even-multiplicity theorem has been presumed.

## 4. The no-common-root branch is strictly positive

It remains to consider the case in which there is no common unit-circle root. Put

`Q(z)=sum_j |q_j(z)|^2` for `|z|=1`.

At every circle point at least one summand is strictly positive, so `Q(z)>0` everywhere on the circle. Pad each `q_j` with zero coefficients through index `m`, and define, for `-m<=r<=m`,

`c_r=sum_j sum_{u,v in {0,...,m}, u-v=r} (q_j)_u conj((q_j)_v)`.

Finite expansion, using `conj(z)=z^(-1)` on the circle, gives

`Q(z)=sum_{r=-m}^m c_r z^r`,

`c_(-r)=conj(c_r)`, and

`c_0=sum_j sum_{u=0}^m |(q_j)_u|^2>0`.

The last inequality follows because at least one polynomial has a nonzero coefficient. Thus there is a largest `ell` in `{0,...,m}` with `c_ell!=0`. Conjugate symmetry shows that all coefficients outside `[-ell,ell]` vanish and that `c_(-ell)!=0`.

If `ell=0`, then `Q=c_0` on the circle. The positive real constant polynomial `sqrt(c_0)` is the desired factor. There is no root-pair argument in this constant case.

Suppose `ell>=1`. Define the ordinary polynomial

`P(X)=sum_{r=-ell}^ell c_r X^(r+ell)`.

Then `degree(P)=2ell`, `P(0)=c_(-ell)!=0`, and on the circle

`P(z)=z^ell Q(z)`.                                       (F1)

Conjugate symmetry also gives the exact polynomial identity

`P#_(2ell)=P`.                                           (F2)

By (F1) and strict positivity, `P` has no roots on the circle. Its nonzero constant term excludes zero as a root.

## 5. Reciprocal-root pairing with all multiplicities

Let `S` be the full multiset of roots of `P`; the fundamental theorem of algebra gives its cardinality `2ell` and the product factorization

`P=L product_{alpha in S} (X-alpha)`, with `L!=0`.

Every root is nonzero. Reflect and conjugate the complete product, using the fixed degrees of its factors:

`P#_(2ell)=conj(L) product_{alpha in S} (1-conj(alpha)X)`

`          =C product_{alpha in S} (X-tau(alpha))`,

where `tau(alpha)=1/conj(alpha)` and `C=conj(L) product_{alpha in S} (-conj(alpha))!=0`.

Taking root multisets and using (F2) proves

`S=S.map(tau)`.                                          (F3)

This proves multiplicities, not just equality of root sets: product factorization and the roots-of-product multiset identity retain every repeated occurrence.

The involution `tau` exchanges roots inside and outside the unit circle, because `|tau(alpha)|=1/|alpha|`. There are no zero or circle roots. Let `M` be the submultiset of roots with `|alpha|<1`. Equation (F3) says that the complementary outside multiset is exactly `M.map(tau)`. Hence

`S=M+M.map(tau)` and `2 card(M)=2ell`, so `card(M)=ell`.

Define the monic polynomial

`h_0=product_{alpha in M} (X-alpha)`.

It has degree `ell`, nonzero constant term, and no circle roots. Its fixed-degree reflection is

`h_0#_ell=product_{alpha in M} (1-conj(alpha)X)`.

Thus `h_0 h_0#_ell` and `P` have identical full root multisets and degree `2ell`. Applying their full product factorizations gives a nonzero constant `kappa` such that

`P=kappa h_0 h_0#_ell`.

For `|z|=1`, the reflection evaluation identity and (F1), followed by cancellation of the nonzero `z^ell`, imply

`Q(z)=kappa |h_0(z)|^2`.                                 (F4)

Evaluate at `z=1`. Both `Q(1)` and `|h_0(1)|^2` are positive real numbers. Therefore `kappa` is the embedded positive real number

`beta=Q(1)/|h_0(1)|^2>0`.

Set `h=sqrt(beta) h_0`. Equation (F4) proves the required equality on the whole circle, and `degree(h)=ell<=m`. This completes the strict branch and the induction, hence also the original weighted factorization.

The proof chooses all inside roots by their modulus; it does not select one representative of a pair ambiguously, assume roots simple, or invoke a root-isolation computation. Classical existence/choice and the already proved fundamental theorem of algebra suffice.

## 6. Strong polynomial identity consumed by the GMRES proof

Apply the elementary reflection identity with the common degree bound `m`. The circle equality from factorization implies

`h h#_m=sum_j w_j h_j (h_j)#_m`                           (F5)

as an exact polynomial identity: on the circle both sides equal `z^m` times their respective modulus-square functions, and that circle is infinite. This remains valid when `degree(h)<m`, some inputs vanish, all weights vanish, or `m=0`.

Equation (F5), rather than an integral interchange, is the most direct interface to the subsequent Euclidean norm and full complex orthogonality identities. Its proof must use the common fixed degree `m` throughout.
