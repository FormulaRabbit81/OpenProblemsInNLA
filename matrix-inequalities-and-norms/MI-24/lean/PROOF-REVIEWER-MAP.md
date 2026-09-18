# MI-24 source guide for full independent review

This is an author-prepared navigation guide, not an independent verdict or an
execution certificate. Run receipts, source hashes, kernel/Comparator evidence,
and nonauthor reviews must be assessed separately.

The original target is the complete Schatten complement inequality on **every
complex positive definite pair**, in every positive dimension, for **every real
`p >= 1` and for the infinity endpoint**. `Definitions.lean`, `Challenge.lean`, and
`comparator.json` retain their exact statement-first local289 bytes. The historical
draft notices in the frozen files are preserved as part of that boundary.
`Solution.lean` imports the completed proof modules and requests an axiom report
and kernel-trust assertion for each of the 22 frozen contracts. It does not
redeclare, weaken, or replace their statements.

## Reading order and all frozen contracts

| Contracts | Sources | Actual content to inspect |
|---|---|---|
| C01 | `Numerical` | Two kernel-mode LeanCert bounds on the single interval `[0,1/2]`; their instantiated complement-weight bound is used in C09. |
| C02 | `SpectralPowers` | Concrete positive spectral powers and genuine matrix inverse, including negative real powers. |
| C03–C06 | `MeanPositivity`, `GeometricCongruence`, `HalfFixedPoint` | Positivity of all eight matrices, Riccati characterization of the actual geometric mean, arbitrary invertible congruence, explicit half-power fixed point, and actual square root of `powerHalfQ`. |
| C07 | `PolarPowers`, `OrderPowers`, `FurutaBase`, `FurutaHalfPower` | The needed bounded Furuta theorem is proved inside Lean, using polar CFC identities, inverse order and Löwner–Heinz, followed by the finite exponent extension. It is not a citation premise. |
| C08 | `HeronOrder`, `HeronNorm`, `CompoundAlgebra`, `DiagonalPowers`, `CompoundSpectral`, `CompoundNorm`, `ScalarLogMajorization`, `WeightedTrace` | The full weighted trace inequality is obtained from the true order implication at every compound degree and proved scalar logarithm summation. Details below. |
| C09 | `TraceSpectral`, `TraceOverlap`, `TraceYoung` | Exact two-basis trace expansion and nonnegative unitary overlap weights with both marginals; scalar weighted AM–GM consumes C01 through `youngWeight_complement_bounds`. |
| C10 | `HeronTrace` | Average the two C08 inequalities using the proved fixed point and square root; apply C09 and cancel the strictly positive Young weight. |
| C11–C13 | `PowerScaling`, `TraceHolder`, `PositivePowers`, `PositiveSchatten` | Actual PSD Schatten norm monotonicity, triangle inequality and homogeneity. The `p=1`, zero scalar and singular PSD cases are included. Matrix Hölder is derived from the same spectral overlaps and scalar Hölder. |
| C14, C16 | `OperatorNorm` | The actual Euclidean operator norm, PSD order monotonicity, and equality to the first actual singular value. |
| C15 | `FiniteSemantics` | The frozen trace-of-modulus formula equals the sum of the actual singular values to every real `p >= 1`. Applies to arbitrary complex matrices, including singular ones. |
| C17 | `HeronFinite` | The complete finite-p Heron input follows from C10 and positive homogeneity. |
| C18 | `HeronInfinity` | Explicit finite-power contradiction, with proved trace bounds; no Schatten-limit theorem is assumed. |
| C19 | `PolarModulus`, `LinComparison` | Actual polar-modulus order comparison, transformed into the original ordered Lin/geometric-mean formulas. |
| C20–C22 | `Complement` | The exact middle matrix is the average of the Heron and right endpoints. C17/C18, C19, order monotonicity and the actual triangle inequalities yield both original conclusions and their conjunction. |

## The substantial C08 bridge

`HeronOrder` defines the two literal positive comparison matrices `S` and `T`.
The actual C07 theorem proves `T <= 1 -> S <= 1`. `HeronNorm` scales the input by
the positive target norm and proves `norm S <= norm T` without dividing by zero.

`CompoundAlgebra` defines entries as actual minors, identifies those entries
with the exterior-power linear map, and proves multiplication, adjoint, unitary,
and diagonal identities. `CompoundSpectral` gives a concrete unitary
diagonalization of the compound with all eigenvalue products. Real powers,
including negative powers, commute with this actual compound on positive
definite matrices. Applying the norm comparison in compound dimension is legal
because `k <= n` implies that dimension is positive.

`CompoundNorm` does not assume that the chosen eigenbasis already has sorted
indices. It constructs the explicit equivalence to Mathlib's descending list,
sorts each finite subset, bounds every product by the leading product, and
exhibits a subset attaining that product. This proves the compound-norm formula,
including degree zero and its empty product.

`ScalarLogMajorization`, authored by agent `/root`, proves the scalar transfer.
Prefix-product inequalities give nonpositive prefix sums of `log a - log b`.
The scalar logarithm tangent inequality bounds `a - b` by `a * (log a - log b)`;
finite summation by parts with descending positive `a` proves sum domination.
`WeightedTrace` uses this theorem and explicit cyclic trace identities to reach
the literal C08 conclusion. No matrix log-majorization theorem or trace
comparison is an added premise.

## Boundaries and computations

- The original hypotheses require positive definite inputs, so inverses and
  real negative powers have their genuine positive-spectrum semantics.
- Norm lemmas needed on the PSD cone cover singular matrices, zero traces,
  scalar zero, and the separate `p=1` case. They are not abstract norm axioms.
- Compound degree zero is included; degrees above the dimension are never used
  in the trace comparison. The scalar prefix theorem includes empty vectors.
- C18 first proves `norm(U)^m <= trace(U^m) <= n * norm(U)^m`. If the desired norm
  order failed, an existing natural power of the norm ratio would exceed `n`,
  contradicting C10. Positive dimension and positive definiteness justify the
  denominator; the exponent is proved to be at least one.
- LeanCert performs only two affine bounds on one interval. There is no matrix
  entry enumeration, numerical eigenvalue calculation, or interval subdivision.
- Review concrete CFC/Euclidean/singular-value definitions as well as final
  theorem types; a successful tactic or source scan alone is not a matching
  statement or final runtime certificate.

The principal implementation was written by `/root/nm04_final_referee1`, with
the scalar transfer module authored by `/root`. `/root/mf06_final_referee2` later
contributed the review-requested library reuse and explanatory-comment cleanup.
These source contributors cannot provide independent final code verdicts. Prior mathematical and reused
code credits remain in the individual source headers. George Stepaniants is
credited with his Department of Computing and Mathematical Sciences affiliation
at the California Institute of Technology; no personal email is included.
