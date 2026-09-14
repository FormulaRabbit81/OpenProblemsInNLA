# PR 261: independent AC-02 / AC-03 review

Reviewed 14 September 2026 at head `9bf50028bc30e6cdf78e19089befcb9b9bd6c292`, base `27540c8022a33fef171625b7e48a95e33562d535`. This is a fresh maintainer-side AI review of the submitted arguments and available code, separate from the supplied AI review. It is not human peer review, Lean verification, or a novelty assessment.

**Verdict: accept the two notices and retained research artifacts with their present limitations; keep both problems Open.** Neither exact complex bilinear rank nor exact complex border rank of 3-by-3 multiplication is determined. No new endpoint follows. No blocking error was found in the restricted scopes accepted by the notices. Their difficulty and importance flags remain consistent with the retained targets. No source or canonical files were changed by this audit.

## AC-02: supported scope

I read the complete 979-line round-one report and 685-line continuation, the supplied review and relevant code/certificate formats. The complete round-one checker was inspected before execution and freshly passed, as did all seven regression tests. These checks use exact integer/rational identities and justified one-sided modular rank certificates, not numerical residuals.

- Both 23-term schemes satisfy all 729 Brent equations. Nonzero-forcing traces and triangular pairwise Khatri–Rao certificates apply to their fixed supports. The Laderman torus computation includes integral lattice/inverse checks, all Laurent identities, the 58-dimensional parameterization and the 52-dimensional gauge normalization with a six-dimensional slice. It does not classify arbitrary 23-term schemes or all 22-term candidates.
- The component argument correctly combines the 76 independent integral family directions, the exact identity `JH=0`, and a nonzero 545-by-545 Jacobian minor modulo the checked prime 1,000,003. The associated family has dimension 76 and meets a smooth point. The polynomial trace signature is constant on that component closure and excludes finite-coefficient zero-slot limits there. This is a component-specific obstruction.
- The reshaping identity proves the output-rank-sum lower bound. In the output-tight case, the square factorization gives all block biorthogonality identities. The stated profile restrictions depend on output tightness; they are not universal restrictions on every rank-22 algorithm.
- The continuation's defect-projector identity and the conditional obstruction from retaining the four designated Sun blocks are sound. I independently expanded all nine polynomial identities expressing the minors of U in minors of the stacked Sun matrix. Thus a compatible additional block of rank at least two leads to the stated contradiction.
- Both displayed five-block sets satisfy all 100 scalar compatibility equations and their five output factorizations over the rationals. Their stated coefficient-matrix ranks are correct. I also checked explicitly that neither five-block set alone is a multiplication algorithm.

Independent code in this review imports submitted data only. It separately reconstructs the 729 coefficients for Laderman, Sun and the supplied rational family point, then checks a newly chosen 58-parameter rational point with mixed signs and nonunit values. An intentional coefficient corruption is rejected. These supplementary samples corroborate the fully symbolic supplied torus certificate; samples alone are not its proof.

### AC-02 claims excluded from certification

The continuation contains larger statements that must remain excluded from the passing audit: the two complex noncompletion theorems for the five-block sets (Theorems 6.1 and 7.1), the asserted complete algebraic case covers and pairings behind them, and the full parameter-family/certificate claims requiring the missing continuation machinery. There is no delivered round-two code directory containing `check_all.py`, `verify_all_two_completion.py`, the other referenced verifiers or the advertised 20 tests. Base and pairing JSON records are present, but records alone do not validate the completeness of their algebraic reductions. The referenced `five_family_polynomial.json` is absent. The TeX inputs `sun_matrix.tex`, `yz_table.tex`, `family_uv.tex`, and `example_a_data.tex` are absent, preventing independent rebuilding of that report from this source tree. Exploratory floating-point residuals prove neither a rank-22 algorithm nor nonexistence.

These limitations are already explicit in the canonical notice and report cover. The retained original report's stronger internal claims must be read with that boundary; this audit does not upgrade them to verified results.

## AC-03: supported scope

I read the complete 1,128-line latest report, the supplied review and the available runner/obstruction code. The current combined runner was freshly executed in scratch and fails at its first missing module, as disclosed. The supported elementary arguments can nevertheless be checked directly.

- For the pair plane E, the repeated diagonal H blocks give rank at least three times rank(H). A rank-one Segre tangent vector has matrix rank at most two, forcing H=0. The tangent intersection is precisely the small Segre tangent space; regularity proves the scheme-theoretic section is reduced. The length/span argument then gives the stated cactus-rank obstruction. I independently reconstructed E, checked dimension 17 and checked the tangent intersection at eight coordinate points and a noncoordinate rational point; the general conclusion rests on the written rank argument.
- For the four-factor plane, I reconstructed all 27 multiplication coordinates and the 16 disjoint core coordinates. All 17 extra lambda-monomial minor witnesses hold, and an independent exact computation of the complete restricted quadratic span has rank 63. This supports the displayed restricted ideal. Saturation removes the cone-vertex class, while limits of spans can still exceed the span of the limiting scheme. Cactus rank therefore must not be substituted for border rank.
- The Fourier compression formula works by exact character orthogonality: every surviving exponent is nonnegative and its complete constant tensor is the prescribed compression tensor. Conciseness gives the matching grouped rank 17. Independent expansion for all three physical groupings obtains all 43 constant coordinates and the residual coefficient totals **272, 236, 272**. At parameter t=1 and Fourier index zero, each merged factor has matrix rank four. Thus these formulas do not decompose that factor into the original two factors and do not prove four-factor border rank 17.
- The auxiliary control tensor has grouped border rank 17 by the same construction and conciseness, while the rank-at-least-seven versus tangent-rank-at-most-two argument gives its cactus obstruction. It correctly illustrates the logical gap and is not an asserted solution for the original tensor.
- The additional pair-plane implications in Theorem 2.1 are valid conditional on the inherited exhaustive classification premise. The projection and concise-flattening continuity steps are sound. This audit does **not** certify that computational premise, so it does not endorse an unconditional reduction of every border-rank-17 algorithm to this single plane.

### AC-03 claims excluded from certification

The latest `code/` contains only `verify_all.py`, `exterior_obstruction.py`, and `grid_obstruction.py`. Missing files include `section_geometry.py`, `pair_geometry.py`, `grouped_degeneration.py`, `wild_control.py`, `cyclic_third_order.py`, `toric17_verify.py`, `test_consistency.py`, `check_manifest.py`, `requirements.txt`, `modular.py`, and `exact.py`. The full certificates directory, including `grid_joint_kernel.json`, is absent. The two obstruction programs therefore cannot independently validate their advertised computations in this delivery.

Excluded claims include the exhaustive inherited Borel/chart classification, all 24 normalized cyclic exclusions and their exterior-rank certificates (Theorem 6.1), the grid-plus-barycenter kernel/quadratic/cubic certificate (Theorem 7.1), and the exhaustive monomial Fourier exclusion (Theorem 8.1). The nested prior archives were inventoried and CRC/path checked, but their exhaustive mathematical classification was not re-certified. Stored result JSON and historical PASS labels are not substitutes for complete reproducible certificates. The canonical notice and supplied review correctly preserve this distinction.

## Sources and presentation

The imported baseline claims are consistent with the primary sources inspected: [Sun's explicit rank-23 construction](https://arxiv.org/html/2604.27645v1), [Bläser's survey](https://theoryofcomputing.org/articles/gs005/gs005.pdf), and [Conner–Harper–Landsberg, Theorem 1.1](https://arxiv.org/html/1911.07981), which gives the border-rank lower bound 17. The caution about finite-scheme spans versus limiting spans also agrees with [Buczyńska–Buczyński, Sections 7.2–7.3](https://arxiv.org/html/1910.01944v2). These sources are used for the stated imports; this was not a new exhaustive literature or novelty search.

All seven relevant PDFs were rendered and visually inspected: both one-page canonical PDFs; the 17-page AC-02 round-one report; the 21-page continuation and its 22-page wrapper; and the 18-page AC-03 report and its 19-page wrapper. Wrapper body pages were independently confirmed pixel-identical to their source report pages. This gives 60 unique inspected pages. Canonical notices and cover limitations are legible, and no canonical layout fix is needed. A nonblocking awkward line break in the original AC-02 continuation title-page status box splits “Principal”; the original material is preserved. The continuation's exploratory residual also differs slightly between its TeX (`0.00979617984743414`) and PDF (`0.00979618193029806`), reinforcing that its numerical records are not certified mathematical conclusions. Neither discrepancy affects the accepted exact scope.

## Evidence and reproduction

All 51 AC-02 and 15 AC-03 delivered payload files match the submitted provenance hashes. This establishes integrity relative to the submitted manifest; original outer ZIP files were not delivered, so their recorded hashes were not independently recomputed. The two nested AC-03 ZIP files pass CRC, path traversal and symlink checks. The source worktree remains clean.

Run with Python 3.10+ and NumPy/SymPy installed:

```sh
python reproduce.py --repo /absolute/path/to/reviewed/checkout --out /absolute/path/to/new/evidence
```

The portable runner checks source payload hashes before and after, uses a fresh temporary copy, reruns the complete supported round-one checker and seven tests, records the expected AC-03 failure and its missing-file child log, and runs this review's independent checks. It does not run numerical searches or claim to certify missing artifacts.

Compact evidence to retain: `review.md`, `reproduce.py`, `independent_checks.py`, `independent-checks.json`, `independent-checks.log`, `ac02-round1-rerun.json`, `ac02-tests.log`, `ac03-runner.log`, `ac03-first-child.log`, `hash-receipt.json`, `inventory.json`, `pdf-raster-equality.json`, and `SHA256SUMS`. The scratch copies and rendered/contact images are local inspection aids and need not be committed.
