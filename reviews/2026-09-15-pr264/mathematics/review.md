# PR 264: independent mathematical audit of MF-24

**Verdict: PASS. The manuscript gives a complete negative answer to MF-24's original uniform-boundedness target. `Solved` is warranted for that target, with the exact dimension-dependent constants and their optimal growth still explicitly open. No mathematical correction is required. No Lean verification or external human peer review is established by this audit.**

Reviewed on 15 September 2026 at exact source commit `32b028cf16e210f8f628ab1cc7c8f5b389df0632`, against published base `6d840cd6bdf811e166ba0a07501407fb121ff0ce`. I read the complete `references/mf24-counterexample/proof.tex`, all four pages of `proof.pdf`, the canonical MF-24 page and its fixed-base version, and the supplied self-review and independent-review report. The analysis below was checked directly; the supplied `PASS` claims are not premises. The source checkout was read only.

## Exact target and scope

The original `matrix-functions-and-stability/MF-24/README.md` defines super-identical pseudospectra by equality, with multiplicities, of **all** singular values of `A-zI` and `B-zI`, for **every complex** `z`. It defines `C_N` using spectral operator norms and one common polynomial `p`, with `p(B) != 0`. The explicit admission target is whether `sup_N C_N` is finite. The matrices and polynomial may depend on dimension. The original page retains sharp constants as a related quantitative question, rather than making their determination a prerequisite for answering boundedness.

The manuscript uses exactly this definition and these quantifiers (Theorem 1, PDF p. 1; TeX lines 33–95). For every integer `m >= 2` and real `t > 1`, it constructs positive weighted upper shifts of order `N=(m+1)^2`, with `N-1` weights, and a common polynomial of degree `m(m+2)=N-1`. Real rational witnesses at `t=m` are admissible complex matrices and polynomials. The fixed-base problem statement and context/definitions are unchanged in the submitted canonical page.

## Equality of every shifted singular-value list

The all-size argument is sound (Lemma 2 and equations (6)–(10), PDF p. 2; TeX lines 97–170).

For the specified upper shift, direct multiplication gives a tridiagonal shifted Gram matrix with diagonal `u, u+w_1^2, ...` and off-diagonal product `|z|^2 w_j^2`. Its leading determinants therefore satisfy the stated recurrence with `u=|z|^2+eta`, including the initial cases `d_0=1`, `d_1=u`. The transfer product is ordered correctly: a later edge multiplies on the left.

Independently expanding `R=v f^T+a w g^T` and `S=v f^T+b w g^T` gives

```math
RS-SR=(b-a)\{v(f^Tw)g^T-w(g^Tv)f^T\}.
```

Sandwiching by `f^T` and `v` cancels the two terms because they are the same product of commuting scalars. The two-by-two Cayley–Hamilton identity expresses every `R^n` as a scalar combination of `R` and `I`. Thus the sandwiched commutator identity extends to every nonnegative integer power. This needs no inverse, division, distinct eigenvalues, or nonzero shift.

For the literal words, the motif transfer is `P=K(1)^(m-1)K(t^2)` and the two total products are precisely `f^T R^(m-1) S v` and `f^T S R^(m-1) v`, with `a=t^(-2)` and `b=1`. The lemma equates their entire determinant polynomials in `eta` for each fixed complex `z`. Substituting the characteristic-polynomial variable then gives equal eigenvalue multisets of the Hermitian positive semidefinite Gram matrices. Taking their nonnegative square roots proves equality of every singular value, including zeros and multiplicities. The argument covers the continuum of complex shifts and every allowed `m,t`; it is not inferred from sampled determinants or SVDs.

## Polynomial norm ratio and nonzero denominator

The height and unique-path formulas are correct (equations (11)–(14), PDF p. 3; TeX lines 172–221). The first motif edge increases the prefix height by one, and each inverse bridge decreases it by one. The displayed height formulas therefore cover all vertices, including motif endpoints. A polynomial monomial occupies one distinct superdiagonal, so there are no unaccounted cancellations or duplicate contributions.

At each of the `m` vertices `j(m+2)`, the X-height is two. The first row of `p_m(X)` consequently has `m` entries `t^2`; its Euclidean norm gives the lower operator-norm bound `t^2 sqrt(m)`. For Y, the entry from vertex zero to vertex `N-1` is exactly `t^2`. Thus `p_m(Y)` is nonzero for every allowed parameter and the ratio is always defined.

The denominator estimate is a genuine spectral-norm estimate (PDF p. 3, following equation (14); TeX lines 205–253). Residue classes modulo `D=m+2` have size `m` or `m+1`, and every forward pair in one class occurs in the polynomial. The Y-height-zero vertices have distinct residues `-q`; the height-two vertices have distinct residues `s-m`. Hence each block contains at most one height zero and at most one height two, with all others one.

Removing a block's zero first column and zero last row preserves its operator norm. The resulting matrix is entrywise bounded by the nonnegative outer product with factors `t^(-a_i)` and `t^(a_(j+1))`. Componentwise absolute values followed by Cauchy–Schwarz prove the norm domination also for complex input vectors. Since `L>=2` and `t>1`, the two squared factor norms are at most `1+(L-2)t^(-2)` and `t^4+(L-2)t^2`, even if an exceptional height is absent. Their product is exactly `(t^2+L-2)^2`. Taking the maximum over residue blocks yields `||p_m(Y)|| <= t^2+m-1`. No Frobenius-norm replacement or unjustified entrywise operator inequality occurs.

## Completeness of the negative resolution and Corollary 3

Equation (15), PDF p. 4 / TeX lines 255–263, already settles the original target. For the finite rational choice `t=m`, the ratio is at least `(4/5)sqrt(m)`, since `4(m-1)<=m^2`. Given any proposed finite nonnegative universal bound `C`, an integer `m>=2` with `m>(5C/4)^2` gives a strict counterexample. An unbounded subsequence of dimensions is sufficient to refute uniform boundedness; no convergence of matrices or attainment of a supremum is needed.

Corollary 3 is a valid additional quantitative result (PDF p. 4; TeX lines 265–288). For fixed `m`, the scalar lower bounds tend to `sqrt(m)` as finite `t` increases, proving `C_((m+1)^2)>=sqrt(m)` as a supremum statement. It does not assert a finite `t` attains that value. For arbitrary `N>=9`, choose `m=floor(sqrt(N))-1` and pad both matrices by a common zero block. Every shifted singular-value list gains the same copies of `|z|`. Since `p_m(0)=0`, both polynomial matrices gain zero blocks and keep their norms. This proves the stated lower bound for every such `N`, and the liminf follows from `(floor(sqrt(N))-1)/sqrt(N) -> 1`.

## Dependencies, evidence limits, and status

The new argument depends only on elementary finite-dimensional determinant identities, Cayley–Hamilton, singular values of Gram matrices, and the Euclidean operator norm. Its counterexample does not rely on an external nontrivial theorem about pseudospectra. The cited comparison upper bound and definition agree with [Ransford–Walsh, arXiv:2109.14472v2, p. 3, Theorem 1.3](https://arxiv.org/pdf/2109.14472v2); the adjacent discussion and Theorem 1.4 concern similarity-transform conditioning, a different quantity. The new lower scale `N^(1/4)` is compatible with their upper scale `N^(1/2)`.

The [2009 publisher record](https://academic.oup.com/jlms/article-abstract/79/2/511/860814) confirms the terminology and original bibliographic reference. Its full text was not accessible in this audit; I do not claim a fresh inspection of its page 513. This does not leave a dependency gap in the self-contained counterexample or alter its correspondence with the fixed canonical target. The bounded source search is not a publication-priority investigation.

This mathematical audit does not claim to rerun the submitted numerical/exact programs; those are assigned to a separate fresh computation audit. All four manuscript PDF pages were viewed and agree with the argument and theorem/equation locators above. Repository-wide preservation, authorship/affiliation authentication, and final publication/CI checks are separate tasks. The accompanying `receipt.json` pins the exact mathematical source and unchanged canonical target reviewed here.

The repository's `CONTRIBUTING.md` permits `Solved` for a complete argument that passes an independent informal audit, including disclosed AI-agent review. This proof meets the mathematical completeness requirement for a **negative resolution of uniform boundedness**. The retained page should continue to say that the sharp `C_N` and optimal growth rate remain open. Historical difficulty `challenging` and importance `interesting to the community` may remain as ratings of the original question. No `Lean verified` status is supported.
