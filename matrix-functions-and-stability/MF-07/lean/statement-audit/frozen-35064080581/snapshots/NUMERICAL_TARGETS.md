# MF-07: exact numerical and mathematical boundary before proof code

Phase: unapproved statements only. The permanent target is the complete
radius-one assertion in `matrix-functions-and-stability/MF-07/README.md`.
No proof implementation is authorized before two independent statement reviews
and actual remote Linux elaboration. All objects below are complex, all positive
dimensions are included, and matrix families may be infinite.

For dimension d, let `spectralNorm A` be the genuine operator norm induced by
the complex Euclidean norm. For a chronological word `(A₁,…,Aₙ)`, its product
is `Aₙ⋯A₁`. For a nonempty compact family M, define

- `L(M) = sup {spectralNorm A : A ∈ M}`;
- `aₙ(M) = sup {spectralNorm(Aₙ⋯A₁) : Aᵢ ∈ M}`;
- `rₙ(M) = aₙ(M)^(1/n)` for positive n;
- `ρ(M) = inf {rₙ(M) : n ≥ 1}`.

Supremum attainment and the exact equivalence `ρ(M)=1` if and only if the
original root sequence tends to one are mandatory exported obligations. The
infimum definition therefore cannot replace the canonical root-limit semantics
without proving correspondence. The identity singleton must explicitly have
radius one, so the target domain is demonstrably nonempty.

The proposed dimension-only constant is the rational expression

`Θ₁ = 1`, and `Θ_d = d (6d²/(d−1))^(d−1)` for d ≥ 2.

It is larger than Colbrook's displayed constant with `2 exp(1)` in place of 6.
The original question asks for existence of a positive dimension-only constant;
it does not prescribe or optimize that constant. The complete final obligation
is: for every d≥1, every nonempty compact complex family M with ρ(M)=1, every
n≥1 and every selection of n generators from M,

`spectralNorm(Aₙ⋯A₁) ≤ Θ_d (L(M)n)^(d−1)`.

There are no irreducibility, finite-cardinality, diagonalizability, exact
extremal-norm or extra spectral hypotheses. All intermediate approximate-norm
and comparison statements are specialized to radius one, which is exactly the
original MF-07 domain. The manuscript's additional zero-radius nilpotence and
MF-05 Hölder assertions are outside this one-problem draft.

## Only numerical certificate to be computed

`exp_one_bound : Real.exp 1 ≤ 3` is the sole proposed LeanCert interval
obligation. Use kernel trust, the single exact argument 1, and the lowest
sufficient certified precision/Taylor order; there is no search over an interval
of matrices, dimensions, word lengths, norms, singular values or thresholds.
The certificate must be consumed in the proof of the threshold optimization,
using `(1+m/n)^n ≤ exp(m) = exp(1)^m ≤ 3^m` for m=d−1 and n≥1.

With `s = 2d²Ln/(d−1)`, the exact symbolic optimization obligation is

`1 ≤ s` and
`d s^(d−1) (1 + 2d²L/s)^n ≤ Θ_d (Ln)^(d−1)`

for all d≥2, n≥1, L≥1. The inequality L≥1 must come from the proved radius-one
semantics; it is not added to the final problem's premises. All operations
involving variable d,n are symbolic natural powers and real arithmetic, not
finite enumeration. For orientation only, Θ₂=48 and Θ₃=2187; these finite values
are not evidence for the universal result.

## Required proof boundary

1. Exact chronological product and diagonal-inverse semantics.
2. Genuine attained family norm and attained length-n growth, with all-word
   upper bounds and submultiplicativity.
3. Exact radius-one/root-limit equivalence, L≥1, and identity-family semantics.
4. Existence of a finite equivalent approximate extremal norm for every a>1;
   that norm is constructed from actual products, not supplied as a hypothesis.
5. Existence of the source's unitary/positive sorted diagonal coordinates and
   rounded norm with Euclidean equivalence factor d, generator bound a, and
   the actual entrywise bound `L σⱼ/σᵢ`.
6. Triangular damping for positive nonincreasing diagonal weights, retaining
   arbitrary full diagonal blocks. This does not assert norm contraction for
   general unstructured matrices.
7. The exact all-word expansion bound from bounds on every C-segment and each
   E-factor; empty C-segments are included.
8. The source comparison `aₙ ≤ d s^(d−1) (1+2d²L/s)^n` for every s≥1 and n≥0.
9. The scalar dimension endpoint, the consumed exponential certificate,
   symbolic threshold optimization and positivity of Θ_d.
10. The complete growth bound and an explicit theorem with the original
    `∀d ∃Θ_d ∀M ∀n ∀A₁,…,Aₙ` quantifier order.

No definition or theorem premise assumes any of these conclusions. Intermediate
existence theorems are independent obligations, not unchecked seed data.
