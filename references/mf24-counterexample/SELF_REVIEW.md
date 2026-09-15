# Self-review of the MF-24 counterexample

No mathematical defect was found in this review. This is a self-review within the same AI-assisted development process, not an independent referee report. The proposed status is **Solution claimed**, not **Solved** or **Lean verified**. The reviewed source hashes and actual check output are recorded in [verification.txt](verification.txt).

## Scope and quantifiers

The original target asks for a constant uniform in dimension, the matrix pair and the polynomial. The construction uses a single common polynomial for each pair and lets it depend on dimension, as permitted. Its degree is exactly $`N-1`$. The matrices are real, hence admissible complex matrices, and the $`(0,N-1)`$ entry of $`p_m(Y)`$ is $`t^2`$, so the denominator is nonzero. Unbounded similarity condition numbers are not being substituted for an unbounded polynomial norm ratio.

Equation (15) uses the finite rational choice $`t=m`$ and already disproves uniform boundedness. The limit $`t\to\infty`$ is used only for the lower bound on a fixed-dimensional supremum in Corollary 3. Zero padding is justified by $`p_m(0)=0`$. No exact value or optimal asymptotic rate for $`C_N`$ is asserted.

## Algebraic points checked

The Gram determinant recurrence uses squared weights and the conjugate product $`|z|^2w_j^2`$. Later edges multiply on the left, which fixes the motif product and the two bridge orders. The resulting identity is an identity in the full characteristic-polynomial variable for every complex shift, not just equality of determinants at selected arguments.

The transfer matrices need not commute. Only the displayed sandwiched commutator vanishes. The two-by-two Cayley–Hamilton identity extends this equality to every nonnegative power. This step makes no division or invertibility assumption, so zero shifts, singular transfer matrices and repeated eigenvalues are not exceptions.

## Norm points checked

The height formulas use one-based edges and zero-based vertices consistently. Every supported polynomial entry comes from exactly one monomial. Every pair of distinct, ordered vertices within a residue class occurs in the polynomial, because each block has size at most $`m+1`$.

The denominator estimate is an operator-norm bound. After the zero first column and last row are removed, the remaining matrix is dominated entrywise by a nonnegative rank-one matrix. The manuscript explicitly proves the resulting norm domination for complex vectors. Each block has at most one height zero and one height two, giving the two Euclidean factor bounds. Neither a Frobenius norm nor an entrywise bound is silently substituted for the operator norm.

## Computational checks and their limits

The exact script uses a second edge-by-edge construction, full bivariate determinant polynomials, direct Gram characteristic polynomials with the complex shift and its conjugate kept symbolic and ordinary matrix powers. At $`m=t=4`$ and $`m=t=9`$, the full bivariate shifted-Gram identities are rechecked for those particular pairs, and exact positive rational $`LDL^{\mathsf T}`$ factorizations certify the strict ratios $`>32/19`$ and $`>243/89`$. A misplaced-bridge control retains the weight multiset but is rejected; a zero pivot is also rejected.

The floating-point script uses explicit matrix operator norms, compares the block calculation with dense matrix powers and checks finitely many complex shifts. Its normalized absolute singular-value errors are not relative-error guarantees for very small singular values. The large-order table uses small residue blocks, not dense order-10,000 shifted SVDs. The scaled block entries avoid forming $`t^2`$ at extreme floating-point parameters.

## Literature and formal-verification limits

The MF-24 entry and Ransford–Walsh's arXiv v2 were inspected. The 2009 paper's publisher metadata and abstract were checked; its full text was not obtained. The canonical entry's page-513 attribution is retained as the repository's source record, not presented as a fresh inspection of that page. Section 5.3 of [Pal–Yakubovich, arXiv:1609.08325v2](https://arxiv.org/abs/1609.08325v2), manuscript p. 16, provides a later historical statement of the uniform-boundedness question; it is not a current-status certificate. Bounded searches found no later resolution, but do not establish priority.

The written proof is self-contained apart from elementary linear algebra. It has not been independently refereed or verified in Lean. Supporting algebra scripts from an earlier uncompiled, incomplete Lean draft are intentionally excluded from this submission.
