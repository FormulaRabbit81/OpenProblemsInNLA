# RA-02 independent mathematical preflight

**Approve the finite arrowhead route for precise statement design.** No mathematical defect was found in its full negative-target argument. This is a review of a mathematical proposal, not approval of Lean statements or code, a completed formalization, or a verification-count change. Reviewer `/root/mf22_publication_referee` did not author the route and did not rely on the other referee's verdict.

I read the complete canonical RA-02 page and all mathematical content of the 637-line retained manuscript (the contact-bearing author-header line was omitted from display), then independently checked every formula in FINITE-ROUTE.md. The two private snapshots were matched byte-for-byte to literal upstream commit `ce47b5630bf3680d9211131c3a43825b022c139a`. Exact reviewed proposal and snapshot digests are in SOURCE-CHECKS.json. Original resolution credit remains Matthew J. Colbrook, Cambridge DAMTP. This route need only refute the full original polynomial-factor assertion; it does not establish the manuscript's sharp supremum, entrywise-positive, correlation-matrix, or LU extensions.

## Positive definiteness and the actual eigenvalue tail

For arbitrary integer r>=1, t=1/(2r+1) lies strictly between zero and one. Consequently epsilon=t^(2(r+1)), every d_i and every alpha_i are positive. The displayed quadratic form is exact. Its complex version is

`sum_i d_i |x_i+alpha_i x_r|^2 + epsilon^r |x_r|^2`.

If it vanishes, x_r=0 and then every x_i=0, so the actual complexified matrix is Hermitian positive definite. The vector q=(-alpha_0,...,-alpha_(r-1),1) is nonzero and has Rayleigh quotient `epsilon^r/(1+sum_i alpha_i^2) <= epsilon^r`. Thus the actual smallest Hermitian eigenvalue is positive and at most epsilon^r. Since n=r+1, the actual rank-r eigenvalue tail consists of exactly that one eigenvalue. The eventual contracts must use genuinely ordered real Hermitian eigenvalues and prove this identification; an assigned surrogate “tail” would not be faithful.

## Actual updates, probabilities and cancellation

Before selecting the distinguished label, an ordinary pivot i has diagonal d_i. The rank-one update removes its row/column and subtracts exactly d_i alpha_i^2 from the distinguished diagonal. The proposed arrowhead state is therefore preserved.

Once the distinguished label has been selected, write `c(U)=epsilon^r+sum_(i in U) d_i alpha_i^2`. The remaining block is `D_U-v_U v_U^T/c(U)`. Its i-th diagonal is exactly `d_i c(U\{i})/c(U)>0`. Substitution in one ordinary-pivot update changes the common denominator from c(U) to c(U\{i}), giving precisely the claimed state. Selected rows/columns stay zero. The remaining block is positive definite when U is nonempty: weighted Cauchy–Schwarz bounds the subtracted quadratic term by `(1-epsilon^r/c(U))*sum_i d_i|x_i|^2`. Hence the zero-padded residual is PSD, every unselected diagonal is positive, and every selected diagonal has zero sampling probability.

For r distinct pivots there is exactly one unselected label. If it is the distinguished label, the ordinary pivot product times the final residual is `epsilon^r*product_i d_i`. Otherwise, the distinguished c(U) pivot and successive denominator ratios telescope, ending in `d_j epsilon^r/c({j})`. The same product D results. Multiplying the actual conditional probabilities gives `product(pivots)/product(prefix traces)` without any independence assumption, so each complete history's probability times final trace is exactly `D/product(prefix traces)`.

The eventual formalization must still supply a finite path distribution or kernel and connect its expectation to the canonical law. It may define an arbitrary harmless update for zero-probability zero-diagonal choices, but those branches must receive probability zero. For an actually zero residual it must keep the residual zero; a dummy label distribution can normalize the path measure. General PSD sampling semantics and nonnegative omitted contributions must be established, rather than simply defining the expected error as the retained-history sum. For the counterexample itself every distinct prefix of length at most r has positive trace, so the zero-residual case is not encountered on its positive-weight paths.

## The exact history count

A concise bijection uses a carried label. Start with carry c_0=r. At time u, the two allowed pivots are u and c_u. If u is chosen, keep the carry; if c_u is chosen, replace the carry by u. Inductively the selected set after s steps is `{0,...,s-1,r}\{c_s}`, with c_s either r or an ordinary label below s. Thus the two choices are distinct and unselected at every step. Different binary strings first differ at a pivot with two distinct options, so they yield distinct histories; conversely every retained history determines these choices. This proves exactly 2^r histories and both prefix-state patterns, without enumerating a factorial-sized space.

## All prefix trace bounds, including rank one

Set N=r-s>=1 and F={s,...,r-1}. Since epsilon<=t^2<1,

`sum_(i in F) epsilon^(i-s) <= 1+(N-1)t^2`.

If the distinguished label remains unselected, the weighted alpha sum contributes at most N t^2 and epsilon^(r-s) at most t^2. Therefore `T_s/epsilon^s <= 1+2N t^2`, which is stronger than the proposal's `1+(2r+1)t^2`.

If it has been selected and j<s is the missing ordinary label, expanding the trace gives exactly the numerator displayed in the proposal. The discarded sum is nonnegative; the remaining numerator is nonnegative; and `c>=d_j alpha_j^2>0`, so the stated upper bound follows with the correct inequality direction. After scaling, the extra epsilon term is a power of t with exponent

`2(r+1)(r-s)-2(j+1) >= 4`.

Indeed r-s>=1 and j+1<=s<=r-1. It is at most t^2. Each of the N remaining weighted terms is at most t^2 because i>=s>j. The same bound `1+2N t^2` follows. There is no second case at s=0. At r=1 the sole prefix is s=0, so that edge is fully covered. Selected zero rows do not add to the trace. Empty geometric remainders occur at N=1 and cause no exception.

Finally `(2r+1)t^2=1/(2r+1)<=1/r`, so the desired uniform prefix bound holds for every retained history. To minimize Lean arithmetic, cancel `product_(s<r) epsilon^s` directly against `product_(i<r) d_i`; no triangular-number exponent formula or explicit tiny-rational determinant is needed.

## Full universal negation

The exact history identity, 2^r retained paths, and nonnegative other contributions give

`E trace(R_r) >= 2^r epsilon^r/(1+1/r)^r >= (2^r/3) epsilon^r >= (2^r/3) tau_r(A)`.

The sole fixed numerical certificate may be exp(1)<=3. The preceding binomial-to-exponential comparison is symbolic in r. No spectral computation, interval grid, or limit in the matrix parameter is needed.

For every real C>0 and every real p>=0, exponential growth over natural r gives some integer r>=1 with `2^r>3 C r^p`. The actual tail is strictly positive, so the displayed expected-error lower bound strictly exceeds `C r^p tau_r(A)`. This is a counterexample in dimension r+1 to the complete universal statement over all PSD complex inputs, all dimensions and all permitted target ranks. Restricting the constructed witnesses to real positive-definite matrices is valid for this negation. The final Lean theorem must retain arbitrary real p and negate the original universal claim; neither an integer-only exponent nor a helper ratio theorem alone would finish RA-02.

## Supplementary checks and remaining gates

I executed audit_preflight.py. It independently checked the two literal Git source bindings and used exact Fraction arithmetic for r=1,2,3,4: 30 retained terminal histories and 52 actual rank-one updates in total. It checked the closed residual states, positive active pivots, selected zero probabilities, normalized conditional probabilities, every retained prefix bound, the exact telescoping contribution, and the finite expectation lower bound. It also checked the explicit q quadratic form. These tiny tests are supplementary; the universal argument above, not finite enumeration, supplies the mathematical justification. No numerical eigensolver, local Lean or Lake, heavy enumeration, or purported universal proof certificate was used.

The mathematical route is suitable for the user's computation-minimizing strategy. The remaining semantic work is substantial but concrete: exact finite sampling, the true eigenvalue-tail bridge, symbolic arbitrary-r inequalities, and arbitrary-real-power domination. Precise numerical/semantic contracts require two independent approvals and an actual statement elaboration before proof implementation. Fresh duplicate/PR checks, frozen statements, LeanCert consumption, full kernel/axiom and Comparator runs with controls, two nonauthor final proof reviews, formalization.yaml, and exact published-commit verification remain outstanding. This is a scoped independent AI mathematical review, not official Tau Ceti service execution, human peer review, or a new priority claim. No candidate source, status, Git ref, PR, or verification count was changed.
