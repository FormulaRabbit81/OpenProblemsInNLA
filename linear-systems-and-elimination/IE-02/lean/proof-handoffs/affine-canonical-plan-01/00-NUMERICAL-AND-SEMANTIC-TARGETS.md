# IE-02 attained affine and canonical Jordan minimax: targets before code

Author: George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, with substantial OpenAI Codex assistance.
Original mathematical and library attribution remains in the frozen
Definitions.lean and SourceCorrespondence.md. This is a source-only implementation
plan; no proof source, compiler result, or completed-target claim is produced.

## Exact frozen contract 44: affine_minimax_attained

For every n ≥ 1, every k ≥ 0, every lower triangular complex Toeplitz matrix Y,
and every k-tuple of complex Toeplitz directions R, put
A(c) = Y − Σ_j c_j R_j, with arbitrary complex coefficients c_j. Norms are the
actual Euclidean vector and induced operator norms already fixed in Definitions.
The two scalar quantities must keep their actual extrema definitions:

  I = inf_c ||A(c)||₂,
  W = sup_{||x||₂=1} inf_c ||A(c)x||₂.

Prove I = W and supply all frozen attainment witnesses. Every unit vector has an
attaining inner coefficient tuple. One common tuple c₀ and unit vector x₀ must
simultaneously attain the operator minimum, the outer maximum, the operator norm
of A(c₀), and the vector minimum at x₀. Explicit inequalities must certify their
global minimizing/maximizing properties for all complex tuples and all unit
vectors. A zero minimizing residual remains allowed. Repeated, dependent, and
zero directions, including the empty tuple k = 0, remain allowed. No uniqueness,
rank, strict positivity, or compactness of the coefficient parameter space is
assumed.

The zero-residual case must exhibit a unit vector using n ≥ 1 and prove its zero
vector residual is minimal by norm nonnegativity. The nonzero case must use the
proved full complex orthogonality conclusion of contract 41, then actual
Pythagoras to show that the same operator-minimizing tuple also minimizes the
vector residual. Real-part stationarity alone is not silently substituted for
that complex orthogonality statement.

## Exact frozen contract 50: canonical_jordan_minimax

For every n ≥ 2, every nonzero complex lam, and every integer 1 ≤ k < n, let
J = lam I + the upper Jordan shift. The admissible polynomials are all complex
polynomials of degree at most k with p(0) = 1, including lower-degree choices.
Prove the actual worst-case GMRES value equals the actual ideal GMRES value:

  sup_{||x||₂=1} inf_{p(0)=1, deg p≤k} ||p(J)x||₂
    = inf_{p(0)=1, deg p≤k} ||p(J)||₂.

Retain all frozen hypotheses and every attainment clause. Every unit vector has
an admissible polynomial attaining its inner minimum, with the comparison
against every admissible q. A single admissible p₀ and unit x₀ must attain the
ideal minimum, ||p₀(J)||₂, and the worst-case value, while satisfying all three
global comparison clauses. These are numerical norm extrema of matrix polynomial
evaluation, not definitions replaced by the desired equality.

Transport is through the actual reversal isometry between upper and lower Jordan
matrices and the exact two-way normalized-polynomial residual parameterization.
Equality of actual value sets must precede equality of their infima or suprema.
The lower problem uses Y = I and the powers of the lower Jordan matrix, whose
Toeplitz membership is already proved. No restriction to real coefficients,
sampled vectors, finitely many shifts, or unattained extrema is permitted.

## Computation and prerequisite limits

These two contracts need only symbolic linear algebra, finite sums, order facts,
and existing attained-minimum theorems. No new interval computation or numerical
certificate is needed. The one genuine kernel-mode LeanCert certificate already
used in the descent chain remains the only numerical certificate in this route.
No source for 44 or 50 will be implemented before root accepts this plan and
the exact prerequisite minimizer_orthogonality (41) passes the root's serial local
compiler. All 13 frozen inputs and pins remain unchanged; final Comparator and
independent proof review remain separate later obligations.
