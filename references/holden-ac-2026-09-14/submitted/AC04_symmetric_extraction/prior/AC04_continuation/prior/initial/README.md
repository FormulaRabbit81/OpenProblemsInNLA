# AC-04 research package

**Status: partial result, not a solution or disproof of AC-04.**

The original question asks whether the complex small Coppersmith–Winograd tensor has asymptotic rank exactly 3. This package does not establish that equality. It contains a written derivation of

\[
3\leq\widetilde R(\mathrm{cw}_2)<3.923038,
\]

using Alman and Li's existing slice-extraction framework, a different initial power, and repeated re-extraction. The bound is supported by an analytic all-parameter argument and exact rational certificates. No research-priority, independent peer-review, or proof-assistant-verification claim is made.

## Start here

`report.pdf` is the full mathematical write-up; `report.tex` is its editable source. `AUDIT.md` identifies the proof dependencies, what was checked, and what remains unproved.

The exact scalar certificate uses only the Python standard library:

```sh
python3 code/certify.py --output results/exact_certificate.json
(cd code && python3 -m unittest -v test_certify.py)
```

The additional finite-matrix audit and exploratory table require the optional dependencies:

```sh
python3 -m pip install -r requirements-optional.txt
python3 code/algebra_check.py --output results/algebra_certificate.json
python3 code/explore_bounds.py
```

To rebuild the PDF, use a LaTeX installation with the packages named in `report.tex`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Results included

`results/exact_certificate.json` contains exact rational enclosures proving the strict upper-bound test. It also certifies a narrow bracket for the scalar endpoint and the finite inequalities used in the method-local obstruction.

`results/algebra_certificate.json` records exact coefficient checks, a rank-three flattening, the rank-two signed contraction, the nonsingular 72-dimensional source contraction, and a rank-18 compressed matrix with an explicit nonzero minor.

`results/tests.log` records eight passing regression tests. `results/exploratory_bounds.csv` contains high-precision values, which are not used as proof of a strict inequality. Decimal fields in the certificate are display-only; the actual comparisons use integers and rational numbers.

## Important limits

The recurrence admits a formal value 3.9 for every iteration. This is a limitation of that particular scalar-constraint family, **not** a proof that the tensor's asymptotic rank is at least 3.9.

The surviving task is to prove or disprove asymptotic rank 3. A positive proof still needs rank growth `3^(k+o(k))`, or an equivalent statement. A rank bound on a fixed small power, a formal feasible scalar assignment, and a better constant above 3 are not interchangeable with that target.

The repository was read through public web pages and was not modified. This is not a repository resolution submission. The package contains no third-party paper copies or font files.

## Sources

The precise source locators and URLs appear in the report bibliography and `sources.json`. The main comparison is to Alman–Li's displayed bound below 3.931 and their Table 1 value 3.930872; it is not a claim to have ruled out every other optimization.
