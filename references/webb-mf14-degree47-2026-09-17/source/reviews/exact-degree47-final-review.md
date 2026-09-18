# Independent final review: the exact seven-product degree is 47

17 September 2026. Reviewer: `/root/c3_equal_review`. This reviewer did not
author the degree-47 chart, its numerical search, its rational seed, the
author's exact certificate implementation, or the dimension argument.
The final manuscript was read completely, including the clarification
that the contraction varies exactly the 48 active coordinates. No author
proof or certificate source was edited by this reviewer.

**Verdict: no unresolved mathematical gap identified in the reviewed
scope. The exact target in `TARGET.md` is resolved: `d7=47`.**

The proof establishes both `V47 subset X7` and `V48 not subset X7`,
where `X7` is the complex Zariski closure of outputs with at most seven
products in the full coefficient space `V128`. These are the required
quantifiers and ambient space. The result is not an assertion that every
degree-47 polynomial has an exact seven-product representation, or an
assertion about real coefficients, stable recovery, or a projected image.

The final proof is independent of the earlier four- and five-product
auxiliary theorems and of the external general dimension theorem. Its
dependency chain is the explicit actual-circuit chart, the rational
contact certificate, the full weighted coefficient limit, and the
generic available-space dimension upper bound.

## 1. Actual seven-product chart

The first product computes `x^2`. The second is
`x^2*(x^2+alpha*x)=Q=x^4+alpha*x^3`. In the third-product identity put
`g=b-1`, `sigma=(eta-c+alpha*g)/(b-2)`, and `rho=c-sigma`.
Expanding its displayed product gives

```
Q^2 + (g+1)*x^2*Q + (rho+sigma)*x*Q
    + g*x^4 + (rho+g*sigma)*x^3 + rho*sigma*x^2.
```

Subtracting `g*Q+rho*sigma*x^2` cancels the degree-four correction
and gives the degree-three coefficient

`rho+g*sigma-g*alpha = c+(b-2)*sigma-g*alpha = eta`.

Thus it is exactly the claimed `R`. Every factor and subtraction uses
only `1,x,x^2,Q`; there is no free computation of an unavailable `x^3`.
The identity holds on `b!=2`. Four more products are precisely the four
normalized-factor gates in the code. Their coefficient counts are
6, 8, 10 and 12, followed by nine output coefficients. Together with
`alpha,b,c,eta`, this gives 49 parameters and exactly seven products.

The resulting map `Phi:C^49 -> V128` is polynomial even at `b=2`.
The dense open actual-circuit construction and polynomial continuity
place its entire image in `X7`. The certificate also keeps its whole
ball away from `b=2`, so its root lies in the actual chart. No assertion
that this chart is dense in all of `X7` is needed for the lower bound.

## 2. Independent exact reconstruction

I read `lower_full49_certify.py` and its imported integer arithmetic
helpers. I independently implemented
`reviews/full49-degree47-fresh-check.py`, importing only my own earlier
review's elementary Gaussian-integer polynomial arithmetic. It imports
no author implementation and uses no NumPy, decimal refinement, root
search, or floating-point arithmetic in its assertions.

The fresh checker evaluates all **129 output coefficients** through
degree 128. It reconstructs all **49 derivative columns** by reversing
the four normalized product gates. For a gate `q=L*R` with current
adjoint polynomial `w`, its left/right sensitivities are `w*R` and
`w*L`; the previous top polynomial receives their sum, while each
earlier basis polynomial receives its two scalar-weighted sensitivities.
The factor-parameter columns are the corresponding sensitivity times
the selected basis polynomial. After this reverse pass, writing the
adjoints of `Q,R` as `wQ,wR`, the first four columns are

```
d_alpha = [wQ+wR*(2Q+b*x^2+c*x)]*x^3,
d_b     = wR*x^2*Q,
d_c     = wR*x*Q,
d_eta   = wR*x^3.
```

The output-parameter columns are the nine available basis polynomials.
This is a different derivative implementation from the author's forward
jets. It preserves every coefficient throughout its computation.

The 49 input Gaussian rationals have denominator `10^70`; the inverse
matrix has denominator `10^60`. The parameter degree bound is 33,
giving the common output/derivative denominator `10^2310`. Differentiation
is with respect to the actual complex parameters. The independently
computed preconditioned residual, inverse defect and inverse norm agree
**exactly** with the author's rational results. The seed's 48 active
indices are distinct and valid, and the remaining parameter is fixed.

## 3. Contraction and invertibility, with a different Hessian bound

Use `|z|_*=|Re z|+|Im z|`, the maximum of these norms on vectors, and
the matrix row-sum upper bound. This is a complete real normed space
underlying `C^48`; complex multiplication is submultiplicative in this
norm. The author's aggregate derivative triples and product rule are
valid, including the factor two for ordered mixed second derivatives.

The assembled numerical inequalities were also compared with the saved
exact fractions: `eta<10^-69`, `delta<10^-57`, inverse norm `<4000`,
author Hessian bound `<2*10^12`, and author contraction bound `<10^-29`
all hold strictly. These decimal-power comparisons are rational
inequalities, not rounded numerical evidence.

For computational independence, my checker uses a different, much
coarser Hessian proof. Each coefficient of the formal map is a polynomial
with nonnegative integer coefficients in its 49 parameters. Bounding
every parameter norm by `K`, the first polynomial norms are majorized by

`Q(K)=1+K`, `R(K)=1+5K+3K^2`.

For each later gate, its majorant is
`(previous top majorant + K*sum of earlier nonconstant majorants)^2`.
The output majorant `G(K)` is `K` times the sum of the final nine
majorants. It has degree 33. Differentiating twice bounds the sum of
norms of all ordered second parameter derivatives of all coefficient
rows, hence also any selected active-row aggregate.

Every parameter has norm at most 4 throughout the certificate ball.
Exact integer evaluation yields

`G''(4)=14225297189516125194807607250462624`.

At radius `r=10^-45`, the independently computed bounds give

`q=delta+||B||*G''(4)*r < 6*10^-8 < 1/2`,

and `eta+q*r<r`. They also verify `|Re(b_c)-2|>r`. Thus the new
check independently establishes the self-map and contraction
inequalities using a different derivative implementation and a different
Hessian bound. Its weaker bound is still ample for the proof.

For completeness, the root conclusion requires the inverse argument:
`delta<1` makes the square complex matrix `B*J(theta_c)` invertible,
so `B` is invertible. Banach's fixed point of
`theta -> theta-B*F(theta)` consequently solves `F(theta)=0`.
The uniform derivative defect at that point is at most `q<1`, making
its selected Jacobian invertible as well. This proves an **exact**
complex contact point with coefficients 0--46 zero and coefficient
47 equal to one, together with rank 48. It does not rely on a numerical
singular value or an approximately zero residual.

## 4. Full coefficient coverage

For each fixed monic polynomial `p in V47`, the holomorphic inverse
function theorem in the 48 active coordinates realizes the low target
vector `p_j*t^(47-j)`, keeping the last parameter fixed. At zero this
target is exactly the certified contact vector, so the local inverse
applies for all sufficiently small `t`; the allowed neighborhood may
depend on the fixed target.

All 129 coefficients of `Phi(theta(t))` are bounded holomorphic
functions near zero. For nonzero `t`, input and output scalings give
`t^-47*Phi(theta(t))(t*x)` in `X7`. The coefficients through 47 equal
those of `p` exactly. **Every** coefficient at degrees 48--128 has a
strictly positive power `t^(j-47)` and tends to zero. This is convergence
in the required full ambient space, not coefficient projection.

Closedness gives the monic target. Output scaling gives every nonzero
degree-47 leading coefficient, and limits through
`p+epsilon*x^47` give lower-degree polynomials. Hence the proof covers
every point of `V47` with the original complex quantifiers.

## 5. Self-contained matching upper bound

I independently audited the generic available-space count. The universal
seven-product map has an irreducible affine parameter domain, including
all at-most-seven-product computations by padding. The conditions of
successive maximal degrees `2,4,...,128` define a nonempty Zariski-open
subset, witnessed by repeated squaring. Its output image is dense in the
full image closure. Thus a dimension bound on this generic image bounds
the entire `X7`; exceptional parameter strata cannot add another
component or a larger image dimension.

After the first gate the available space is `V2`. After the second,
normalization and subtraction of `V2` leave the unique form
`Q=x^4+alpha*x^3`. The family of `W2` spaces therefore has at most
one parameter. Its pairwise-product span is exactly
`V6+C*Q^2`, of dimension eight. Since `W2` has dimension four and
is contained in this product span, a new third-gate space is determined
by a line in a four-dimensional quotient. This contributes at most
three more parameters. The `W3` family has dimension at most four.

For fixed `n`-dimensional `W` containing 1, the factor-pair space has
dimension `2n`. On the open set where `uv notin W`, both factors are
nonconstant. The transformations

`(u,v) -> (a*u+b,c*v+d)`, with `a,c != 0`,

give four-dimensional families of distinct pairs preserving
`span(W,uv)`. The distinctness follows from linear independence of
`1,u` and of `1,v`; preservation follows by expansion modulo `W`.
The fiber-dimension bound therefore makes the enlarged-space family
dimension at most `2n-4` over a fixed `W`. This argument applies in
local vector-bundle charts as `W` varies, so these increments may be
added to the preceding family dimension.

For gates four through seven, `n=5,6,7,8`, giving increments
`6,8,10,12`. The final space family has dimension at most 40, and an
arbitrary vector in its nine-dimensional space contributes at most nine
more. Therefore `dim X7<=49`. The count concerns generic spaces before
image closure; it makes no unjustified assertion about products of
limiting spaces.

If `V48` were contained in `X7`, its dimension 49 would force
`dim X7=49`; irreducibility and strict dimension drop for proper closed
subsets would then force `X7=V48`. Seven repeated squarings give
`x^128 in X7`, contradicting that equality. Hence `V48` is not
contained. Together with the certified lower bound, this proves
**`d7=47`** without using an external dimension theorem.

## Reproduction and final source binding

The independent degree-47 checker passed in this review. Reproduce with

```
python3 'NLA Workspace/mf14-exact-2026-09-17/reviews/full49-degree47-fresh-check.py'
```

It records exact fractions, source hashes and a digest of all reconstructed
full arrays in `full49-degree47-fresh-check.json`. The author checker can
be reproduced separately from the frozen integer seed. Neither search nor
high-precision refinement is required. This review does not claim a
proof-kernel formalization or external human peer review.

No mathematical repair was needed after the independent degree-47
checks. Pending-language removal and the explicit active-coordinate
clarification were read in the final source. The following SHA-256 hashes
bind the exact on-disk bytes, without newline normalization:

| File | Bytes | SHA-256 |
|---|---:|---|
| `proof.md` | 8916 | `d9fb806135cfa84806f207568db6de2270981a9705f43962eeb152f53a14bffa` |
| `TARGET.md` | 2702 | `d75ca7af97277922e035003e2bc3227e0b2f61341fbbcde4e58b6991888574d2` |
| `experiments/lower_full49_seed.json` | 355020 | `4bf9b5cca57fa1f04cf55d49c3308dfc7806a3e98bf3c55faba14ee8209d17c3` |
| `experiments/lower_full49_certify.py` | 4572 | `f79a235f82886d86c849739a0177d89be40e93aa1847591a1c56ec72862b560b` |
| `experiments/lower_contact_certify.py` | 4838 | `7ed564ae8a53a0d4d7b570e0be82e6de4ad5656af33fa85522e00c28b57a1595` |
| `experiments/lower_full49_certify.json` | 23019 | `fdf5a6a2de29664bf8915d1c04560271d8a3428a51941d9cbd3c52f4f88abe52` |
| `reviews/full49-degree47-fresh-check.py` | 7443 | `c8c360905885e63e661cf5341730de37b639a757902ae4acaf3169ade3e2195d` |
| `reviews/seven-contact-fresh-check.py` | 7879 | `da8ce4638d11fdd772b07730d5383a28e0277ab570b78b1d4d43d8db15a06114` |
| `reviews/full49-degree47-fresh-check.json` | 22297 | `200de890653f320800acadcd918551452c996916c1a457876f29829eebef9904` |

The final proof and certificate meet both halves of the current exact
target. Earlier reports remain preserved as source-bound historical
reviews of the smaller-budget and degree-45/46 checkpoints.
