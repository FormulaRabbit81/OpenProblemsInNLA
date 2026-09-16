# IV-03 proof implementation

This development retains the frozen all-dimensional interval criterion. The
main proof follows Colbrook's manuscript, with two exact algebraic replacements
that reduce the calculus and computation required in Lean.

## Closure and completion

`Proof.lean` proves a finite-dimensional maximum principle for a Z matrix B
from a strictly positive vector w with Bw > 0. It derives invertibility and a
nonnegative inverse, then uses the homotopy (1-t)I+tB and determinant continuity
to prove determinant positivity. Missing off-diagonal terms have the needed
sign, so the same positive weight restricts to principal blocks.

`Principal.lean` derives principal inverse-M closure from actual block inverse
formulas. Every block invertibility is obtained from prior closure facts.
Complement enumeration converts an arbitrary finite embedding to a block
partition. Principal Schur complements and both transfer blocks Q D⁻¹ and
D⁻¹ R are entrywise nonnegative.

`Complementary.lean` obtains Jacobi's complementary principal-minor identity
from the block determinant and inverse formulas. `Adjugate.lean` excludes
singularity using rank-nullity and a nonzero codimension-one principal minor:
the adjugate would have rank at most one, whereas a Z matrix with positive
diagonal and order at least three has rank greater than one. A negative
determinant would give negative principal inverse minors and contradict an
exact three-by-three determinant inequality. Thus positive proper principal
minors and nonpositive off-diagonal adjugate entries imply det A > 0, without
assuming regularity.

## Cofactors without regularity

`Cofactor.lean` replaces one row by a coordinate vector. The determinant of the
result is the relevant adjugate entry by Mathlib's definition. Eliminating an
invertible complementary block D leaves a 2x2 determinant whose value is the
negative off-diagonal Schur entry. This proves

    adj(A)[i,j] = -det(D) * Schur(A)[i,j]

without inverting A or passing through a density/continuity argument.

## Exact box comparison

`Monotonicity.lean` uses the identity

    D⁻¹ - E⁻¹ = E⁻¹ (E-D) D⁻¹.

For lower/upper rows l ≤ u and columns c ≤ v, the bilinear difference is

    u D⁻¹ v - l E⁻¹ c
      = (u E⁻¹)(E-D)(D⁻¹ v)
        + (u-l)(E⁻¹ v) + (l E⁻¹)(v-c).

Every factor needed on the right has a proved nonnegative sign. In
`SchurInterval.lean`, E is the actual complementary block and D its lower
endpoint. Three explicit matrices in the original interval replace the
retained row or column by its upper endpoint. Their proper principal blocks
supply the transfer signs. Therefore the Schur entry at an arbitrary interval
member is at least the corresponding tested vertex entry.

`IntervalStructure.lean` proves exact principal compatibility of vertices.
`IntervalAdjugate.lean` combines the box comparison with the cofactor formula.
`IntervalInduction.lean` assembles strong induction, using the explicit order
one and order two cases in `Vertices.lean`. `Solution.lean` exposes exactly the
four frozen theorem statements and requests LeanCert kernel trust checks and
axiom reports for each export.

No numerical interval approximation, decidability shortcut, regularity
assumption, placeholder, or additional mathematical axiom is needed. Build and
audit receipts, rather than this explanation, determine verification status.
