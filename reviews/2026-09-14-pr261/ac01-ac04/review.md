# PR 261: independent AC-01 and AC-04 audit

**Verdict: PASS for inclusion as partial research; neither original problem is solved or Lean verified.** No blocking mathematical or presentation error was found in the two current reports or their canonical notices. Difficulty `extreme`, importance `broadly interesting`, and status `Open` remain appropriate for both unchanged targets.

Reviewed source: PR head `9bf50028bc30e6cdf78e19089befcb9b9bd6c292`, against published base `27540c8022a33fef171625b7e48a95e33562d535`, on 14 September 2026. The source worktree was read only. This is an independent AI-agent mathematical audit, not external human peer review, a priority assessment, or proof-assistant verification.

## Target correspondence and claims

AC-01 asks whether complex arithmetic straight-line matrix multiplication has exponent two, with an algorithm of cost `O(n^(2+epsilon))` for every positive epsilon. The submitted AC-01 report instead proves the auxiliary small-CW upper bound `Rtilde(cw_2) < 3.876919161` and an obstruction for its explicitly defined scalar recurrence relaxation. Neither gives an exponent-two algorithm or a tensor-rank lower bound. The exact exponent-two target and all its quantifiers survive unchanged.

AC-04 asks the exact equality `Rtilde(cw_2) = 3` for the specified complex three-tensor. Its own report proves `Rtilde(cw_2) < 3.896914` and local decomposition results; the canonical page correctly cross-references the stronger AC-01 bound. An upper bound strictly between three and four, a contraction obstruction in an algorithm class, and a local fiber classification do not settle this equality. The current notices state these boundaries explicitly and preserve prior-source credit. Reaching three would imply the central exponent-two breakthrough, so the existing difficulty and impact flags remain justified.

## AC-01 mathematical review

I read the complete current report, including all-size proofs and the appendices, and the supplied AC-01 review. The following points were checked independently rather than inferred from a supplied `PASS` record.

* The paired six-term tensor `P` is equivalent over the complex numbers to the canonical `cw_2`. Spectral points are used additively; asymptotic rank itself is never assumed additive. The tight-support subrank estimate supplies a lower bound on every spectral point, permitting subtraction from a direct-sum spectral inequality.
* The initial Fourier exchange cancels every negative Laurent block, including the auxiliary-head contribution. Composing the two exchanges with the first parameter equal to the seventh power of the second leaves positive error order. The resulting state has active dimension 108, residual size 112, contraction rank 328, and source spectral upper bound 330.
* The radical-aware extraction distinguishes actual main dimension from dimension modulo the contraction radical. Its head condition survives tensor products; the complementary paired form is constructed in the nonsingular quotient. The rational reflection argument applies to nonzero isotropic vectors and extends the paired basis without treating radical rows as additional active directions.
* The non-coordinate core has the claimed zero Gram matrix. The retained tensor is exactly `P` times the complete-bipartite tensor `Z`, giving the extra spectral factor `phi(P)`. Its tight weights and uniform marginal entropy yield the claimed all-size lower estimate. The proof uses grouped three-mode products throughout.
* The mixed recurrence and its three squaring steps give the displayed active dimensions, residual sizes, and source costs. Independent rational cube-root enclosures with denominator `10^55`, generated without reading the submitted radical records, give a final normalized positive gap `5.0738862358540418763e-9` at `3.876919161`. This exceeds the requested `1e-9` margin. Monotonicity and continuity of the recurrence give a strict bound for the maximum spectral value. The stronger unsupported candidate `3.876` fails this certificate.
* The all-binary-tree claim is proved by the written product-envelope induction, not by the finite sampled trees. At `x = 913/250`, independent exact comparisons validate its constants and a leaf slack exceeding `0.2075985371290280794`. It is a feasible scalar assignment for that relaxation, not a spectral point, a lower bound on asymptotic rank, or a barrier to other uses of the tensor relations.

The fully stored `20 x 25` example was independently expanded over all 8,000 ordered output coefficients. Its 66 constant coefficients are exactly those of `P^2` plus `C_10`; 450 coefficients have positive degree and all negative coefficients vanish. The map has rank 20. This finite example illustrates extraction; it is not substituted for the written all-size proof.

## AC-04 mathematical review

I read the complete current report and the supplied AC-04 review. The symmetric Fourier extraction produces the literal direct sum `P^n + C_(4^n + 2^n - 2*3^n)` from `D_(4^n) + C_(2^n)`. Its negative-degree cancellation, paired-form congruence, and explicit border decomposition agree. The interpolation consequence bounds the rank of powers of the **direct sum**; it does not improperly subtract ordinary rank.

At the fourth power the spectral inequality is `phi(P)^4 + phi(C_110) <= 274`, with `phi(C_110) >= 3*cuberoot(3025)`. The resulting fourth-root bound and its exact rational bracket pass independent polynomial sign checks. Optimality at `n = 4` is limited to the stated uniterated estimates; the separate AC-01 construction is compatible with it.

The local symmetry theorem uses the connected Fourier-charge graph and the implicit function theorem near the specified standard decomposition. The second-power symmetric derivative has rank 128 and kernel dimension 16. Independently reconstructed charge blocks have ranks 5, 7, and 9 as claimed; adjoining the four mixed columns gives rank 13 in every doubly nonzero charge. All nine induced cokernel maps are invertible, with determinant `-1296` in the displayed first block.

Crucially, the two-branch conclusion does not rely on a quadratic obstruction alone. Both adaptive axes solve the full tensor equation exactly. After solving the normal equations, the residual analytic equations vanish on both axes, hence factor through the 36 mixed products. The resulting coefficient matrix is invertible near the origin. This proves that the reduced local fiber is exactly the two axes: two smooth ten-dimensional symmetric branches, with four-dimensional intersection. Adding the 32 ordinary rescaling parameters gives the stated dimensions 42 and 36. The global component statement is restricted to components through the standard point, using closed monomial torus images; it does not classify distant decompositions.

The full-spark argument follows from the absence of nonzero rank-one slices of `P`. Its block-minor rank inequality proves the fully supported adaptive contraction bound and, with induction allowing zero weights, `K <= s^2`. These conclusions do not prohibit a distant nonadaptive rank-three contraction. Exploratory failed numerical searches are not used as proofs.

## Primary dependencies checked

The spectral maximum characterization and degeneration compatibility were checked against [Christandl–Vrana–Zuiddam, Theorem 1.1 and Remark 1.2](https://arxiv.org/html/1709.07851). The same source's Theorem 4.4 and Corollary 4.5 provide the tight three-tensor entropy/subrank result. The ordinary, not merely monomial, formulation was also checked in [their graph-tensor paper, Theorem 1.1.31](https://arxiv.org/html/1609.07476v2).

[Alman–Li, Theorem 1.2 and Section 4](https://arxiv.org/html/2605.21738v1) support the implication from small-CW asymptotic rank three to exponent two and the spectral framework; their Table 1 supplies the previous published numerical comparison. [Dupont et al., abstract](https://arxiv.org/abs/2608.16884) reports `omega < 2.371177`, as the AC-01 context states. These external results are mathematical dependencies, not formalized by the supplied Python. A bounded search located no resolution of either original equality; that search is not a certification of global open status.

## Fresh execution and visual checks

The submitted programs and nested archive paths were inspected before execution. The two complete runners were then executed in disposable copies. AC-01 passes all coefficient, rational-form, cube-enclosure and envelope checks, rejects ten supplied corruptions, and reruns its preserved earlier pack. AC-04 passes both new certificate jobs, 40 new tests, 25 inherited tests, eight initial tests, and the optional inherited SymPy algebra check.

The separate reviewer script imports no submitted checker. In addition to the AC-01 checks above, it reconstructs the AC-04 Laurent expansion for powers one through five. At power five it enumerates 1,048,576 source group terms and verifies all 9,486 constant terms and negative-degree cancellation, extending the submitted literal range. Its adversarial checks reject a scaled main row, a changed head exponent, reversed padding, and the unsupported numerical bound. The independent derivative reconstruction and endpoint tests also pass. Finite checks complement the general written arguments; they are not Lean verification.

All 19 AC-01 report pages, all 16 AC-04 report pages, both submission covers, and both canonical pages were rendered and visually inspected. Mathematical content, status notices, and limitations are readable, with no clipping or missing equations found. The historical source packs remain available; the current reports reprove the dependencies needed for the new bounds, and the inherited finite suites were rerun. No global audit of every historical exploratory claim is asserted.

## Reproduction and evidence

Requires Python 3.10 or later and SymPy. The recorded environment was Python 3.12.14. From this review directory run:

```sh
python3 reproduce.py --repo /path/to/repository --out /path/to/new-audit-output
```

This copies only the two submitted packs into temporary scratch, runs the supplied and independent checks, writes compact logs/results, and removes the temporary copies. It does not edit the repository. `independent_checks.py` also accepts `--repo` and `--out` directly. Do not use Python's `-O` option: the reviewed finite checks use assertions.

The compact evidence comprises `reproduce.py`, `independent_checks.py`, `reproduction/` logs and JSON results, and `receipt.json`. The receipt records exact source hashes and checks that both canonical target sections and flags match the fixed published base. The mathematical acceptance above is specifically for the reviewed source revision and stated partial scope.
