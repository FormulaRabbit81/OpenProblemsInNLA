# RA-02: a smaller symbolic counterexample route for review

**Status: mathematical proposal only, independently unreviewed.** Root has read the full canonical problem and Colbrook manuscript from literal upstream ce47b563. No Lean statements, proof implementation, formal verification or priority claim is made here. Original mathematical resolution credit remains Matthew J. Colbrook, Cambridge DAMTP. This alternate construction is a proposed AI-assisted formalization route for the same complete negative target; it does not claim the manuscript's stronger sharp supremum or entrywise-positive/correlation-matrix extensions.

The original question asks whether fixed C>0 and p>=0 work for every PSD matrix and every target rank. To refute it, an explicit real positive-definite family with ratio at least 2^r/3 for every r>=1 suffices. It is unnecessary to formalize the stronger exact limiting ratio 2^r, LU, all nonprincipal minors, or correlation-matrix replication. A counterexample subset is logically sufficient for this universal assertion; the final exported theorem must still negate the entire original universal statement.

## 1. Explicit arrowhead family

Fix an integer r>=1; index the matrix by the r ordinary labels i=0,...,r-1 and the distinguished last label r. Put

`t = 1/(2r+1)`, `epsilon = t^(2(r+1))`, `d_i = epsilon^i`, `alpha_i = t^(i+1)`.

All these scalars are strictly positive and 0<t<1. Define the real symmetric (r+1)-square matrix by

- A_ij = d_i if i=j<r and zero if i!=j<r;
- A_ir = A_ri = d_i alpha_i;
- A_rr = epsilon^r + sum_(i<r) d_i alpha_i^2.

For every real x, its quadratic form is

`sum_(i<r) d_i (x_i+alpha_i x_r)^2 + epsilon^r x_r^2`.

It is strictly positive for nonzero x. Complexification is Hermitian positive definite as well. The fixed vector q with q_i=-alpha_i, q_r=1 has quadratic form epsilon^r and squared Euclidean norm at least one. Hence the smallest eigenvalue satisfies

`0 < lambda_min(A) <= epsilon^r`.

Because the order is r+1, the original rank-r tail is exactly lambda_min(A). Prove this with the actual ordered Hermitian eigenvalues and a genuine Rayleigh bound; do not replace the tail by a surrogate definition.

## 2. Exact residual states and positive pivots

Let U be the unselected ordinary labels and let `c(U)=epsilon^r+sum_(i in U) d_i alpha_i^2`, which is positive even when U is empty. Selected rows and columns are zero.

If the last label is unselected, the residual on U together with that label is the same arrowhead formula using U and c(U). Pivoting at an ordinary i in U has value d_i and simply removes i from U. Pivoting at the last label has value c(U) and leaves the ordinary block

`R_ij = d_i*indicator(i=j) - (d_i alpha_i)(d_j alpha_j)/c(U)` for i,j in U.

If the last label has already been selected, the residual has exactly this latter form. Pivoting at i in U has positive value

`d_i c(U\{i})/c(U)`

and gives the same form on U\{i}, with the new denominator c(U\{i}). These identities follow by substituting into the canonical rank-one Cholesky update; all denominators are strictly positive. They establish order independence and all actual probabilities for this family directly. No general Schur-complement or Cauchy-minor asymptotic theorem is required.

For every ordered history of r distinct labels, multiply all r pivot values by its final remaining scalar residual. If the last label is never pivoted, the product is plainly

`D = epsilon^r * product_(i<r) d_i`.

If it is pivoted, its c(U) pivot cancels the subsequent denominator. The factors c(U\{i})/c(U) telescope; the last remaining scalar is `d_j epsilon^r/c({j})`. The same D results. This is an exact identity for actual rank-one updates, not an expectation approximation.

Consequently, with T_s the trace at prefix length s, the probability of a distinct history times its final trace is

`D / product_(s<r) T_s`.

A finite probability kernel or full finite path-weight construction must be supplied and checked against the original conditional sampling law. In particular, positive weights sum to one, selected zero pivots have zero probability, residuals stay PSD, and the zero-residual convention is respected. The final theorem must concern this actual expectation. Nonnegative contributions from other histories may then be discarded in a lower bound.

## 3. Exactly 2^r retained histories

At position u=0,...,r-1 allow either of the unchosen labels in `{0,...,u} union {r}`. There are exactly two: its size is u+2 and the u previous distinct choices lie in it. Thus there are exactly 2^r such histories. Prove a finite counting bijection or two-child recursion; do not numerically enumerate them.

At prefix length s<r, either the last label has not been selected and the selected set is `{0,...,s-1}`, or it has been selected and the selected ordinary labels are `{0,...,s-1}\{j}` for exactly one j<s. The remaining ordinary labels in the second case are `{j} union {s,...,r-1}`. These are the only state patterns needed for the following trace bound.

## 4. A uniform elementary trace bound

For every retained prefix of length s<r,

`0 < T_s <= epsilon^s * [1+(2r+1)t^2] <= epsilon^s*(1+1/r)`.

Here are direct bounds, which avoid all limiting arguments. Write F={s,...,r-1}. Since epsilon<=t^2<1,

`sum_(i in F) epsilon^(i-s) <= 1+(r-s-1)t^2`.

When the last label is unselected, the trace divided by epsilon^s is

`sum_(i in F) epsilon^(i-s)(1+alpha_i^2) + epsilon^(r-s)`.

The additional weighted sum is at most (r-s)t^2, and the final term is at most t^2. This proves the displayed common bound (in fact a slightly better coefficient suffices).

When the last label is selected and j<s is missing, c=c({j} union F)>=d_j alpha_j^2. Cancel the d_j contribution in the trace exactly to obtain

`T_s = sum_(i in F) d_i + [d_j epsilon^r + sum_(i in F) d_j d_i alpha_i^2 - sum_(i in F) d_i^2 alpha_i^2]/c`.

Discarding the last nonnegative subtracted sum and using the lower bound on c gives

`T_s <= sum_(i in F) d_i + epsilon^r/alpha_j^2 + sum_(i in F) d_i alpha_i^2/alpha_j^2`.

After division by epsilon^s, the middle term is

`t^[2(r+1)(r-s)-2(j+1)] <= t^2`,

because r-s>=1 and j+1<=s<=r-1 make the exponent at least four. Every term in the last sum is `epsilon^(i-s) t^(2(i-j)) <= t^2`, since i>=s>j. There are r-s such terms. Combine these with the first geometric bound. The edge s=0 has no second case; r=1 has only s=0. Empty sums, zeros from selected rows and repeated state labels must be handled explicitly in the eventual finite-index proof.

Finally `(2r+1)t^2=1/(2r+1)<=1/r`, so the required trace bound follows without evaluating any large power numerically.

## 5. Exponential ratio and full negative target

For a retained history, the contribution is at least

`D/[epsilon^(sum_(s<r) s)*(1+1/r)^r] = epsilon^r/(1+1/r)^r`.

There are 2^r such histories, so

`E trace(R_r) >= 2^r epsilon^r/(1+1/r)^r >= (2^r/3) epsilon^r >= (2^r/3) tau_r(A)`.

The middle inequality follows from `(1+1/r)^r<=exp(1)<=3`. The last fixed numerical bound can use one consumed LeanCert certificate at the exact point1, already exemplified by MF07. All r-dependent estimates stay symbolic. No factorial-sized path enumeration, long interval computation, explicit tiny-rational determinant or numerical eigensolve is required.

For every C>0 and real p>=0, choose an integer r>=1 with 2^r>3 C r^p, using the standard exponential-versus-real-power asymptotic theorem. Then this explicit positive-definite matrix violates the original bound strictly because its tail is positive. This establishes the full negation with arbitrary C,p; proving only one fixed rank, only bounded p, or the helper ratio would not complete RA-02.

## Outstanding review and formalization requirements

Independently review every displayed algebraic identity and inequality before writing Lean proof bodies. The proposal still needs a fresh public branch/PR duplicate check, exact definitions and all numerical/semantic Challenge contracts, two independent statement approvals, actual statement elaboration and freeze. The full mathematical proof then needs two nonauthor final reviews, actual complete Linux build/kernel/axiom checks, Comparator against the frozen contracts and required rejection controls, truthful formalization.yaml and an exact published-commit rerun/individual upstream PR. None of those gates is claimed here. The source-private manuscript contains its historical author's contact information and must not be republished wholesale.
