# Independent RA-02 arrowhead preflight

**Approve the mathematical route for full statement design. No mathematical error or weakened final target found.** This is a feasibility assessment of an unformalized argument, not Lean verification, statement approval, or authorization to skip any subsequent review gate.

Reviewer: OpenAI Codex agent `/root/ie13_continuation`; route author: `/root`. I made no edits to the proposal. The reviewed `FINITE-ROUTE.md` has SHA-256 `a14770a8d91ad413722ae8cd98339f79b4195ae464fffd00269af1b53bc2162d`. I read the full canonical RA-02 page and all 637 lines of the original Colbrook manuscript, including the Cholesky law, history identity and polynomial-factor negation. Both source snapshots equal literal Git objects at `ce47b5630bf3680d9211131c3a43825b022c139a`. Source hashes and inspected pinned APIs are recorded separately; the private manuscript's contact text is not republished.

## Mathematical checks

The construction addresses exactly the original universal assertion: arbitrary Hermitian PSD inputs, exactly the target rank of pivots, and constants independent of dimension, rank and matrix. Exhibiting a real positive-definite family of order r+1 is sufficient to negate that assertion. Off-diagonal zeros among ordinary labels are permitted by the original problem. This route does not establish the original manuscript's stronger sharp supremum, entrywise-positive extension, LU result or correlation-matrix extension, and it does not claim to do so.

For every integer r≥1, t=1/(2r+1) lies strictly between zero and one; ε=t^(2(r+1)), all d_i and all α_i are positive. The stated quadratic identity is exact. Over complex vectors its corresponding identity is

`x* A x = Σ_i d_i |x_i + α_i x_r|² + ε^r |x_r|²`.

If it vanishes, first x_r=0 and then every ordinary coordinate vanishes. Thus complexification really is Hermitian positive definite; no real-only surrogate is required. The vector q=(-α,1) is nonzero, has squared norm `1+Σ α_i²≥1`, and has quadratic form ε^r. A genuine spectral Rayleigh inequality therefore gives `0<λ_min≤ε^r/‖q‖²≤ε^r`. In dimension r+1 the original sorted rank-r tail consists of exactly this one smallest eigenvalue. Positivity of this tail is essential in the final strict contradiction.

Both residual formulas agree with the actual rank-one update. Before selecting the distinguished label, an ordinary pivot removes only its ordinary diagonal and its coupling to the distinguished label, reducing c(U) by d_i α_i². A distinguished pivot gives `diag(d)-bbᵀ/c(U)`, b_i=d_i α_i. Afterwards an ordinary pivot is `d_i c(U\{i})/c(U)>0`. For two other labels, the two rank-one coefficients combine by

`1/c + d_i α_i²/(c c') = 1/c'`, where `c'=c-d_i α_i²`.

Hence the post-update state has the asserted smaller denominator. Selected rows and columns stay zero. These states also have a direct PSD justification: weighted Cauchy–Schwarz yields, on the active ordinary coordinates after the distinguished pivot,

`x*R x ≥ [ε^r/c(U)] Σ_i d_i |x_i|²`.

This is positive for every nonzero active vector. The empty active state is zero. Thus all distinct histories of length at most r have positive unselected pivots and positive trace; zero probability of selected labels is respected. No assumption about nonsingular nonprincipal minors is needed.

The cancellation of pivot values is exact in both cases. Without the distinguished pivot, every ordinary label is selected and the terminal scalar is ε^r. With it, the ordinary pivots before that step contribute their d_i factors, its pivot contributes c(U), and later pivots contribute d_i c(U\{i})/c(U). Their c factors telescope, including when the distinguished pivot is the last step. The final remaining ordinary entry is `d_j ε^r/c({j})`. In both cases the product of all pivots and the terminal trace is `D=ε^r∏d_i`. Multiplying conditional probabilities, without asserting independence, gives the path contribution `D/∏T_s`.

The retained-history count is correct: at position u the available allowed set has u+2 labels and contains all u earlier, distinct choices, leaving two. Different binary choices give different ordered histories, even if some histories later share the same selected set. The prefix characterization is also exact. If the distinguished label is unselected, the selected set is all ordinary labels below s. Otherwise precisely one ordinary label below s remains, in addition to the future labels s,…,r−1. At s=0 only the first case exists.

Every trace estimate has the right inequality direction. In the first state type, the initial geometric term is bounded by `1+(r-s-1)t²`, the α-weighted sum by `(r-s)t²`, and the final ε term by t². In the second type, cancelling the missing ordinary diagonal produces exactly the displayed numerator. Dropping its negative sum and using `c≥d_j α_j²` gives an upper bound. The middle scaled term has exponent `2(r+1)(r-s)-2(j+1)≥4`; every last-sum term is at most t² because i≥s>j and ε^(i-s)≤1. Both types satisfy the slightly stronger bound `T_s/ε^s≤1+2(r-s)t²`; the proposed `1+(2r+1)t²` is safely looser. Since `(2r+1)t²=1/(2r+1)≤1/r`, the final bound follows. Empty sums at s=r−1 cause no problem. When r=1 there is only s=0, so the second case is absent.

Combining the positive trace bounds with the exact cancellation gives at least `ε^r/(1+1/r)^r` per retained history. There are 2^r such histories, and discarded contributions are nonnegative. The inequality `(1+1/r)^r≤exp(1)≤3` then proves the stated `2^r/3` lower factor. For arbitrary real p≥0 and C>0, exponential growth supplies an integer r≥1 with `2^r>3Cr^p`; because the actual tail is positive, the final violation is strict. No bounded-rank, integer-exponent or uniform-in-r limiting assumption is hidden here.

## Required formal contracts and economical implementation

The mathematical preflight succeeds, but the following semantic bridges must be proved explicitly in the statements and implementation:

1. Define the actual complex Hermitian PSD update and normalized conditional sampling law for every input in the original quantifiers. For nonzero PSD residuals, diagonals are nonnegative and trace is positive; weights sum to one. Zero pivots receive zero weight, and a zero residual remains zero. A finite path distribution is sufficient; measure-theoretic machinery is optional if its path probabilities and expectation are fully justified. A recursively defined weighted sum without this normalization/semantic proof would be incomplete.
2. Prove generic PSD preservation for every positive-probability update, then the explicit family-state identities. The generic update can be related to the quadratic form at `y=x-e_j (R_j x/R_jj)`, or to a congruence of R. It cannot be justified solely by positive diagonal entries. Selected-zero and zero-residual cases require their own branches.
3. Define the original tail through actual decreasing Hermitian eigenvalues and prove the rank-r tail equals the last value at order r+1, together with its Rayleigh bound and strict positivity. ε^r is only an upper bound on that tail and must not replace its definition.
4. State and prove the full constants-negation theorem, including arbitrary real p≥0 and the complete original n,r,A range. The explicit family lower bound alone is an intermediate result.

For counting, a two-child construction with a single carried label can simplify dependent finite-set bookkeeping. Initially the carried label is r. At position u the two choices are u and the carried label; selecting u keeps the carry, selecting the carry replaces it by u. The carry is always either r or below u, so these labels are distinct and the bit can be recovered from the output. This proves the 2^r count without enumerating paths.

For the trace-product cancellation, keep `∏d_s` symbolically. It is exactly the same product as the ε^s factors in the denominator, so no triangular-number exponent identity or huge rational normalization is needed. All matrix identities are generic algebra over finite sums. The only numerical certificate proposed is the consumed LeanCert point bound exp(1)≤3; it requires no interval subdivision.

The exact pinned Mathlib sources provide relevant foundations: `Matrix.IsHermitian.eigenvalues₀_antitone`, spectral decomposition and eigenvector bases; `Matrix.PosDef.eigenvalues_pos`; `Matrix.PosSemidef.trace_eq_zero_iff`; quadratic-form criteria and PSD congruence; and orthonormal basis expansion/Parseval identities. The ordinary `eigenvalues` function is reindexed and must not silently be assumed sorted: use `eigenvalues₀` with explicit finite-index transport. No new spectral-theory library is required in principle, although the particular least-eigenvalue Rayleigh comparison still needs an explicit proof or exact reusable lemma.

`PMF.ofFintype`, `PMF.bind_apply` and `PMF.integral_eq_sum` give a standard option for the finite probability bridge. Alternatively, a fully proved finite path-weight kernel can avoid unnecessary ENNReal conversions. `Real.one_add_inv_pow_le_exp` already supplies the rank-dependent exponential inequality. `Real.tendsto_exp_mul_div_rpow_atTop` with positive coefficient log(2), composed with the natural-number embedding, covers arbitrary real exponents. All nine inspected API files match the pinned Mathlib Git commit `0df444a360eaa60ab8c11dca51a86af692955474`; no Lean elaboration was performed here.

## Supplementary checks and recommendation

An independent Python Fraction checker executed actual rank-one updates for r=1,2,3, checking 54 state visits and all 32 terminal histories. It verified normalized conditional probabilities, selected zero rows, both residual formulas and positive pivots, exact cancellation, retained counts 2,4,8, and every retained-prefix trace budget. These finite checks support debugging only; they are not the all-rank proof and compute no eigenvalues. At r=1, t=1/3, ε=1/81, the initial trace is 91/81 and the exact expectation is 2/91, consistent with the asserted bounds.

Proceed to the fresh duplicate audit and full independent statement design. A second nonauthor mathematical review, two independent statement approvals, actual Linux statement elaboration and immutable freeze must precede proof implementation. The route is materially smaller than formalizing all of the manuscript's sharp-limit theorem, while preserving the original negative RA-02 target. The probability semantics and finite bookkeeping remain substantial work; this is a feasibility recommendation, not a completion estimate.

Matthew J. Colbrook retains credit for the mathematical resolution and original manuscript, University of Cambridge DAMTP. The arrowhead construction is clearly identified as this proposed AI-assisted alternative formalization route; no claim that it appears in the manuscript or is historically new is made. George Stepaniants's Caltech Department of Computing and Mathematical Sciences formalization credit remains appropriate when the authorized formalization is prepared. No email, raw manuscript, proof implementation, source edit, local Lean/Lake/cache, Git mutation, workflow dispatch, publication or count change was introduced by this review.
