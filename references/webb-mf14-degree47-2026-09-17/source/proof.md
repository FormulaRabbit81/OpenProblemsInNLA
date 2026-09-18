# MF-14: the exact seven-product degree is 47

17 September 2026. **Computer-assisted theorem: d7=47.** The exact rational
certificate and an independently implemented full-coefficient reconstruction
have both passed. The mathematical argument has been reviewed by separate
agents. This is not a proof-kernel formalization or external human peer review.

Let V_d=C[x]_{<=d}. Let P_7 be the outputs obtainable from 1,x using at most
seven products, with arbitrary complex linear combinations free. Let X_7
be its Zariski closure in the FULL space V_128. Define

    d_7=max {d : V_d subset X_7}.

The theorem is d_7=47. The upper bound is proved by a generic available-space dimension count;
the new lower bound has a passing exact certificate and independent
verification. No smaller-budget auxiliary theorem is needed.

## 1. A polynomial family inside the seven-product closure

Use parameters alpha,b,c,eta and define

    q1=x²,
    q2=Q=x4+alpha*x3,
    q3=R=Q²+b*x²*Q+c*x*Q+eta*x3.

The first two products are x*x and x²*(x²+alpha*x). For b!=2 set

    g=b−1, sigma=(eta−c+alpha*g)/(b−2), rho=c−sigma.

Then the exact identity

    R=(Q+rho*x+g*x²)(Q+sigma*x+x²)−g*Q−rho*sigma*x²

computes R with one further product. Indeed the product has cross terms
c*x*Q+b*x²*Q+rho*sigma*x²+(rho+g*sigma)*x3+g*x4;
after the subtractions its x3 term is
rho+g*sigma−g*alpha=eta. All factors and subtraction terms are available.

For k=4,5,6,7, define

    qk=(q_(k−1)+sum_(j=0)^(k−2) u_(k,j)*r_j)
       (q_(k−1)+sum_(j=0)^(k−2) v_(k,j)*r_j),

where (r0,...,r_(k−2))=(x,q1,...,q_(k−2)). Each sum therefore has k−1
coefficients, and each qk costs one product. Finally set

    Phi(theta)=e0+e1*x+sum_(k=1)^7 e_(k+1)*qk.

There are 4+(6+8+10+12)+9=49 complex parameters. Phi is a polynomial map
C^49 -> V128. The explicit construction proves Phi(theta) belongs to P7
on the dense open set b!=2. Polynomial continuity and closedness extend
membership in X7 to every theta, including b=2. No claim about the image
being dense in X7 is needed. No multiplication is hidden in free operations:
all products of scalar parameters are allowed scalar coefficients.

## 2. Exact contact certificate

The frozen file experiments/lower_full49_seed.json specifies a Gaussian-rational
center theta_c, 48 distinct active indices (one parameter is fixed), and a
Gaussian-rational 48-by-48 matrix B. The center denominator is10^70 and the
matrix denominator is10^60. Define

    F(theta)=([x^0]Phi(theta),...,[x^47]Phi(theta))−(0,...,0,1)

and let J be the active-variable Jacobian. In the contraction argument, theta
denotes these48 active coordinates; the remaining coordinate is held fixed.
Use |z|_1=|Re z|+|Im z|,
the maximum vector norm, and matrix row-sum bounds. The exact verifier
experiments/lower_full49_certify.py, using the integer arithmetic helpers
in lower_contact_certify.py, proves at radius r=10^-45:

    eta   = ||B F(theta_c)||              < 10^-69,
    delta = ||I−B J(theta_c)||            < 10^-57,
    ||B||                                < 4000,
    H (aggregate Hessian bound)           < 2*10^12,
    q=delta+||B||*H*r                    < 10^-29,
    eta+q*r                             < r.

It also verifies |Re(b_c)−2|>r, so the entire ball stays within the actual
seven-product chart b!=2. These are exact rational inequalities; printed
floating-point values are diagnostics, not certificate inputs.

To bound second derivatives, propagate nonnegative triples (v,d,h) bounding
the polynomial coefficient-l1 norm, the sum of first-derivative norms, and
the sum of all ordered second-derivative norms. Sums add triples. Products
use

    (v,d,h)*(w,e,k) = (v*w, d*w+v*e, h*w+2*d*e+v*k).

An active scalar parameter starts at (|theta_c,j|_1+r,1,0); a fixed scalar
starts at (|theta_c,j|_1,0,0); each fixed monomial has triple(1,0,0).
Submultiplicativity of coefficient-l1 norms proves the resulting H is a
uniform bound for the full polynomial map. Integrating along a line segment
inside the convex ball gives ||J(theta)−J(theta_c)||<=H*r.

Value/Jacobian calculations can use C[x]/(x48), because this computes the
exact low coefficient equations. The subsequent proof uses the untruncated
Phi of degree128; no truncated polynomial is asserted to be a circuit output.
The parameter-degree bound is33, giving common denominator10^2310 for the
output and first derivatives; derivative numerators are rescaled for actual
parameters, not their integer encodings. All matrix products, norms and
asserted inequalities use Gaussian integers and Fraction arithmetic.

These inequalities prove existence by Banach contraction for
G(theta)=theta−B F(theta). Since delta<1, B is invertible, so its fixed point
theta* solves F(theta*)=0. At theta*, ||I−B J(theta*)||<1, hence J(theta*)
is invertible. Thus a passed certificate proves exact contact of order47
and rank48; numerical convergence alone does not.

The independent verifier reviews/full49-degree47-fresh-check.py imports no
author implementation. It evaluates all129 coefficients of Phi and constructs
all49 derivative columns by a reverse pass through the product gates. It
reproduces the exact preconditioned residual, inverse defect and inverse norm.
Its different positive-polynomial majorant, with every parameter norm bounded
by4, gives the uniform Hessian bound

    14225297189516125194807607250462624.

This coarser bound still proves contraction q<6*10^-8 and eta+q*r<r at the
same radius, and independently checks that b!=2. Thus the exact existence
and rank claims do not depend on the author's derivative or Hessian code.
The numerical search and Decimal refinement are not needed for reproduction:
the frozen rational seed suffices.

## 3. From contact to every degree-47 polynomial

By the preceding certificate, theta* exists with invertible J. Fix ANY monic p in V47.
The complex inverse function theorem, with the remaining parameter fixed,
provides a bounded holomorphic parameter curve theta(t) tending to theta*
with

    [x^j]Phi(theta(t))=p_j*t^(47−j),  j=0,...,47.

At t=0 the prescribed vector is exactly (0,...,0,1), so the inverse applies.
For t!=0 put f_t(x)=t^-47*Phi(theta(t))(t*x). Input scaling and output
scaling preserve P7 and thus X7. The coefficients of degrees0,...,47 are
exactly those of p; for EVERY j=48,...,128, the coefficient is t^(j−47)
times a bounded holomorphic function, and hence tends to zero.

Thus f_t tends to p in FULL V128, and p belongs to X7. Output scaling gives
every nonzero leading coefficient. Any lower-degree polynomial is a limit
of such degree47 polynomials, proving V47 subset X7. This is a full-space
closure argument, not a conclusion from coefficient-projection dominance.

## 4. A self-contained matching upper bound

The universal seven-product circuit parameterization is a polynomial map
from an irreducible affine space. Hence its image closure X7 is irreducible.
It suffices to bound the dimension of its dense generic circuit family;
passing to the image closure does not increase this dimension.

On the nonempty open set with successive degrees2,4,...,128, normalize the
first two available spaces by free changes of basis. After product2 the
space is

    W2=span(1,x,x²,Q),       Q=x4+alpha*x3.

This family has dimension at most1. Its pairwise-product span is

    W2²=V6 + C*Q²,

of dimension8: products of V2 span V4, then xQ and x²Q add degrees5 and6,
and Q² adds degree8. The new third product determines a line in the
four-dimensional quotient W2²/W2. Therefore the family of five-dimensional
available spaces W3 has dimension at most1+3=4.

For any fixed n-dimensional available space W containing1, the next product
has factors u,v in W. The map (u,v)->span(W,uv), defined generically where
uv is not in W, has fibers of dimension at least4. Indeed

    (u,v) -> (a*u+b, c*v+d),     a,c nonzero,

preserves the enlarged space, and gives a four-dimensional family of distinct
pairs when u,v are nonconstant. Thus this step increases the dimension of
the family of available spaces by at most2n−4. Applying this to n=5,6,7,8
gives increments6,8,10,12. Consequently the family of available W7 spaces
has dimension at most4+6+8+10+12=40. An arbitrary output in the resulting
nine-dimensional W7 adds at most9 dimensions. Hence dim X7<=49.

This argument bounds the generic polynomial image and then its closure;
it does not assume limiting multiplication spaces equal products of limiting
spaces, nor exclude exceptional boundary circuits by their degree profiles.

If V48 were contained in X7, its dimension49 and dim X7<=49 would force
X7=V48, by irreducibility and the strict dimension drop for proper closed
subsets. But x128 belongs to P7 by seven repeated squarings and is not in V48.
Therefore d7<=47. Together with the independently verified degree47 contact
and Section3, this gives exactly d7=47. QED.
