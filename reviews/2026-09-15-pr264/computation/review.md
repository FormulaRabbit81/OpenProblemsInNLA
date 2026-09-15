# PR264 computational audit: MF-24 counterexample

Reviewed on 15 September 2026 at source commit `32b028cf16e210f8f628ab1cc7c8f5b389df0632`, base `6d840cd6bdf811e166ba0a07501407fb121ff0ce`. Source directory: `references/mf24-counterexample`.

**Verdict: PASS for implementation fidelity and all reproduced computations; no computational blocker found.** The finite checks support the manuscript's claimed negative answer to uniform boundedness. Their universal mathematical interpretation depends on the separately reviewed all-size proof. This is an independent maintainer-side AI audit, not human peer review, Lean verification, or a novelty/priority assessment.

## Source inspection and environment

I read all four new Python modules before execution: `mf24.py`, `check_exact.py`, `check_numeric.py`, and `independent_check.py`. I also read the complete 311-line proof source, reference README, self-review, supplied independent review and verification record. These scripts perform finite local arithmetic and output results; they contain no network access, shell execution or source mutation. The original generators or preparation helpers mentioned in historical records are not present and were not executed.

Fresh executions use Python **3.12.14**, NumPy **2.3.5**, and SymPy **1.14.0**. Both library versions exactly match `requirements.txt`; the Python version differs from the original recorded runs and is recorded accurately in the receipt. `OPENBLAS_NUM_THREADS=1`, `OMP_NUM_THREADS=1`, and `PYTHONDONTWRITEBYTECODE=1` were set. All submitted scripts ran in copies under scratch, with no changes to the source worktree.

## Submitted verification: fresh results

- `check_exact.py`: PASS. Generic bridge and Cayley–Hamilton identities; independently generated words and heights for m=2,...,30; 18 complete bivariate determinant identities; six direct Gram characteristic-polynomial identities with eta, z and zbar symbolic; six exact dense polynomial/block comparisons; strict rational norm certificates at m=t=4 and 9; misplaced-bridge and zero-pivot controls.
- `check_numeric.py`: PASS. 1,080 complete shifted-singular-value comparisons; worst scaled absolute discrepancy about **1.088e-14**; 24 dense polynomial/block-norm comparisons; 133 norm-bound checks including the coincident t=1 case and scaled t=1e200 case; misplaced-bridge control. The printed seven ratios reproduce the submitted rounded table.
- `independent_check.py --numeric --pdf proof.pdf`: PASS on fresh execution. The submitted reviewer's independent implementation checks 5,247 residue classes, 15 bivariate determinant identities, 54 rational real-shift dense Gram determinants, 280 complex-shift SVD comparisons and 28 dense polynomial pairs. Its new JSON records the actual environment, checker hash, PDF hash and times. The worst scaled SVD discrepancy in this environment is about **3.192e-15**.

I inspected how these checks connect to the proof. The exact checker uses squared weights and a characteristic-polynomial variable, so its determinant checks are stronger than comparing determinant values at one shift. The direct Gram check keeps z and its conjugate independent. The rational positive-LDL computations prove strict upper bounds for the denominator norms for their specific examples; they do not infer positive definiteness from rounded eigenvalues. Rejection checks use explicit exceptions rather than Python assertions, so their logical checks are not disabled by `python -O`. The numerical routine scales polynomial entries before forming t squared, which is why its extreme t=1e200 check remains meaningful in floating-point arithmetic.

## New independent construction and exact evidence

`maintainer_check.py` imports **none** of the submitted code or data. It reconstructs the weights from the displayed height formulas, then uses a different determinant identity from the submitted transfer/Gram-continuant implementation.

The bipartite graph of W-zI is the path C0–R0–C1–R1–... . Each square submatrix has at most one perfect matching because this graph has no cycles. Cauchy–Binet therefore identifies the coefficients of `det(eta I + (W-zI)* (W-zI))` with the weights of all partial matchings. Diagonal edges contribute rho=|z|² and superdiagonal edges contribute Laurent monomials in t². A path-matching enumeration checks every coefficient, retaining **eta, rho and t² symbolically**, without using the submission's two-by-two transfer matrices or Gram continuant.

- The full matching polynomials agree for every m=2,...,8 (N=9,...,81), with respectively 141, 662, 2,163, 5,648, 12,661, 25,406 and 46,867 distinct monomials. Thus these finite-dimensional checks cover all nonzero t and all complex-shift invariants, rather than sampling t or z.
- Twenty-four direct exact dense Gram determinant checks at rational t and real/complex rational shifts agree with the matching polynomial. This independently checks the graph-to-Gram interpretation and conjugation.
- For m=t=4 and m=t=9, exact rational **Sylvester leading-principal-minor** certificates independently prove `(t²+m−1)² I − BᵀB` positive definite for every denominator residue block. All 25 and 100 principal minors, respectively, are positive. Combined with the explicitly reconstructed numerator row, these certify strict ratios **>32/19** and **>243/89**. This uses a different positivity implementation from the submitted LDL code.
- Six direct exact matrix-power evaluations reconstruct every polynomial entry, including all zeros, and verify the degree N−1 endpoint term. The formulas agree for both matrices at m=2,3,4.

Adversarial controls are substantive. Moving the exceptional bridge preserves the entire weight multiset and hence the unshifted singular values, but the full matching polynomial rejects it. At z=1, eta=1 and t=4, the wrong minus correct determinant is exactly `2321634375/64`. A semidefinite matrix with a zero principal minor is rejected by the strict positivity checker. Omitting the highest polynomial degree loses the required endpoint coefficient and is detected. The t=1 specialization collapses to the coincident unweighted-shift control for m=2,...,8.

## Quantifier and coverage boundary

The implementation matches N=(m+1)², m>=2, t>1, and the common polynomial `p_m(z)=sum(z^((m+2)j), j=1,...,m)`. Its degree is N−1, and the denominator's endpoint entry is t², so the denominator is nonzero. Letting the polynomial depend on dimension is explicit. The claim is about the operator-norm ratio itself, not an unbounded similarity condition number.

The all-size conclusion comes from the written bridge identity with Cayley–Hamilton and the universal residue-block norm bound. With t=m the resulting ratio is at least `(4/5)sqrt(m)` and diverges through finite rational examples. One finite ratio greater than one would not suffice. The checks here supply strong independent algebraic evidence and implementation validation; they do not establish an induction for every m or formalize the analytic operator-norm argument. Padding and the limiting supremum bound for each C_N are likewise mathematical consequences to assess in the proof review, not results of finite SVD sampling. Exact constants and optimal growth remain outside the claimed solution.

No relative-accuracy guarantee is claimed for tiny floating-point singular values. No full Lean formalization is included. No missing artifact prevents reproduction of any advertised current checker. Historical README hashes differ because documented review/attribution text was subsequently added; original proof/code hashes in `verification.txt` match the delivered files.

## Reproduction and compact artifacts

With the submitted dependency pins installed, run:

```sh
python reproduce.py --repo /absolute/path/to/reviewed/checkout --out /absolute/path/to/fresh/evidence
```

The runner records source hashes before and after, creates a temporary source copy, runs all three submitted programs and this maintainer checker, and records exit codes, runtime, actual versions and UTC timestamps. It performs no package installation or network action.

Retain `review.md`, `reproduce.py`, `maintainer_check.py`, `maintainer-results.json`, `maintainer-check.log`, `original-exact.log`, `original-numeric.log`, `submitted-independent.json`, `hash-receipt.json`, `reproduction.log`, and `SHA256SUMS`. Scratch copies are local working material and should not be committed. Proof PDF hash: `1ae9316d7c935f6133a54b133d36bc55dce34f3a252b44c314b3b45a54514139`.
