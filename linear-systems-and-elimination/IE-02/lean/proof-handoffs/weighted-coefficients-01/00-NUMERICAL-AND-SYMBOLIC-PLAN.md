# Weighted coefficient preservation: numerical and symbolic plan

This plan precedes any WeightedCoefficients.lean source. Implementation is
held until root acknowledges successful compilation of MaximalSpace02.
Scope: frozen ordinal 29, weighted_coefficient_preservation, exactly.

## Exact semantic and numerical obligations

Set N = d + m and n = N + 1. For arbitrary nonnegative natural d,m,l,k,
complex polynomials a,b,h,q_j,r_i, and arbitrary real weights w_j, retain
all degree bounds on a,b,h,q and the given exact polynomial factor identity

  h * conjReflect m h = sum_j C(w_j : complex) * (q_j * conjReflect m q_j).

Derive both the equality of the actual Euclidean squared coefficient norms
of b*h and the weighted b*q_j family, and preservation of every full complex
inner product between a*h and the actual Toeplitz r_i action on b*h.

There is NO nonnegativity or sum-one hypothesis on the weights in this
contract: the supplied polynomial identity is the only factorization input.
There is NO degree bound on r_i. The finite coefficient vectors and Toeplitz
matrix action retain truncation at n, including all contributions from the
arbitrary direction polynomial. The complex form identity must remain an
equality in complex numbers; taking real parts is used only for the separate
norm conclusion. Empty families l=0 or k=0, zero weights/polynomials,
d=m=0 and bounds greater than actual degree are included. Here n=N+1 is
necessarily positive, so no stronger zero-dimension claim is attached to
this contract. No new numerical certificate, integration, spectral argument,
or factorization existence theorem is needed.

## Symbolic route

First establish a reusable local or private full complex pairing identity.
For a polynomial f of degree at most d and any polynomials b,r, put
  S = conjReflect d f * r * b.
For every g of degree at most m, fixed-bound reflection multiplicativity and
commutative polynomial algebra give
  conjReflect N (f*g) * (r*(b*g)) = S * (g * conjReflect m g).
The product f*g has degree at most N, including when either factor is zero.
The proved coefficient_inner_product identifies coefficient N of the left
side with inner(coeffVector n (f*g), coeffVector n (r*(b*g))).

Multiply the supplied factor identity by S and extract coefficient N.
Finite coefficient linearity and coeff_C_mul yield the weighted sum of the
same full complex pairing for each q_j. This common argument handles both
claims without repeating a coefficient convolution proof.

For the norm claim instantiate f=b and r=1, using hb. The resulting self-inner
product identity becomes the real squared-norm equality after applying
Complex.re, commuting it with the finite sum, and using re_ofReal_mul plus
norm_sq_eq_re_inner. Signed real weights cause no issue in this algebraic step.

For each complex form instantiate f=a and r=r_i, using ha. Rewrite actual
Toeplitz action with toeplitz_action followed by the existing
coeffVector_mul_truncate helper. This bridge holds for arbitrary b*g and r,
so no degree bound or discarded high-degree remainder is added. The resulting
pairing is exactly the frozen conclusion. Use the proved reflection_product
rather than expanding reflection coefficients again.

## Pinned primary reuse

Project theorem dependencies: Coefficients.lean (coefficient_inner_product),
Reflection.lean (reflection_product), and Toeplitz.lean (toeplitz_action and
coeffVector_mul_truncate). Their actual source bytes are bound separately.
Mathlib at pin 0df444a360eaa60ab8c11dca51a86af692955474 supplies:
- Algebra/Polynomial/Degree/Defs.lean:398 degree_mul_le_of_le, with the
  WithBot natural-addition cast identity for the fixed degree N;
- Algebra/Polynomial/Coeff.lean:90 finsetSum_coeff and :156 coeff_C_mul;
- finite sum distributivity and commutative multiplication reassociation;
- Data/Complex/BigOperators.lean:44 Complex.re_sum;
- Analysis/RCLike/Basic.lean:222 re_ofReal_mul;
- InnerProductSpace.norm_sq_eq_re_inner, exported at
  Analysis/InnerProductSpace/Basic.lean:53.

Only small symbolic coefficient extractions and ring/reassociation steps are
planned. No large finite computation, choice of minimizer, or additional
mathematical assumption is introduced. Keep the exact frozen header and all
13 frozen inputs. Preserve George Stepaniants' Caltech CMS affiliation and
all original mathematical and library credits, without email. This is the
proof author's plan, not independent review or executed verification.
