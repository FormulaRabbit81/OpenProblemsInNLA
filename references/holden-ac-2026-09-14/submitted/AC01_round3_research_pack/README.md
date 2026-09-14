# AC-01: non-coordinate residual extraction

**Status: partial research result, not a solution of AC-01.**

The main report derives

    asymptotic_rank(cw_2) < 3.876919161.

It does not prove the matrix-multiplication exponent is two, does not give a new bound on that exponent, and does not establish a lower bound above two. The derivation has not undergone independent peer review or proof-assistant verification.

## Read first

`report/AC01_round3_report.pdf` is the complete mathematical report. Its editable source is `report/AC01_round3_report.tex`. The report states the two external spectral-theory inputs, reproves the initial Fourier exchange, proves the new extraction construction, and separates finite checks from general mathematical arguments.

The new algebraic ingredient is a three-dimensional non-coordinate isotropic matrix space. It retains the exact tensor `P ⊗ Z_(ell_1,ell_2)` in two CW residuals, where `P` is a rational presentation of `cw_2`. The smallest complete example is the rational degeneration

    P^(⊗2) ⊕ C_10  ⊴  C_4^(⊗2).

The archive stores the entire 20-by-25 Laurent-monomial row map for this example.

A separate theorem proves that the explicitly specified scalar tests from the fixed seed admit `rho = 3.652` at every finite binary-tree depth. This is not a tensor-rank lower bound or a constructed spectral point. It limits those tests using their stated lower estimates, not every analysis of the underlying tensors.

## Reproduce the exact checks

From this directory, run:

```bash
python3 code/verify_all.py --output results/verification_rerun.json
```

Python 3.10 or later is sufficient. Only the Python standard library is used. No network access or optional numerical packages are needed. The script exits nonzero on a failed check and prints `ALL CHECKS PASSED` only after completing the suite.

By default, the script also unpacks the preserved round-two archive into a temporary directory and reruns its verifier. To run only the new checks:

```bash
python3 code/verify_all.py --skip-prior --output results/new_checks_rerun.json
```

The recorded successful run is in `results/verification.json` and `results/verification.log`. The exact comparisons use rational arithmetic and integer cubing, not floating-point tolerances.

## What the suite checks

It verifies the isotropic core, rational split bases, all 8,000 possible ordered coefficients of the stored degeneration, six complete literal retained-tensor instances, tight-support weights and marginal counts, the bound's exact recurrence and radical enclosures, the finite premises of the all-tree proof, and ten rejected corrupted or invalid inputs. The largest literal retained instance has 49,284 nonzero ordered coefficients and 4,329 target coordinates per mode.

The enormous later degeneration maps are specified by the general construction in the report, not enumerated. The infinite tree theorem is proved by an analytic product-envelope induction, not inferred from finite tests. The external spectral and tight-support theorems are mathematical dependencies, not formally verified by this code.

## Contents

- `report/`: PDF, editable LaTeX, radical records, and build script.
- `code/`: four standard-library Python modules.
- `certificates/`: exact core, finite degeneration, upper-bound, and tree-envelope certificates.
- `results/`: actual successful verification outputs and rational slack records.
- `notes/`: claim audit, remaining gap, and construction notes.
- `references/sources.json`: primary-source inventory and uses.
- `prior/AC01_round2_research_pack.zip`: the previous pack, including its preserved first round.
- `SHA256SUMS`: checksums of the delivered files other than this checksum file.

## Build the PDF

A LaTeX installation with `pdflatex` and the packages listed in the source is needed only to rebuild the report, not to run the verifier:

```bash
bash report/build_report.sh
```

The script uses a temporary build directory and copies only the resulting PDF back into `report/`.

## The unresolved target

Let `M_2` be the 2-by-2 matrix-multiplication tensor. AC-01 requires

    rank(M_2^(⊗n)) = 4^n exp(o(n)),

or an equivalent proof of exponent-two arithmetic complexity. This statement is not proved here. The sufficient small-CW route would require `asymptotic_rank(cw_2) = 3`, which also remains unproved in this package.
