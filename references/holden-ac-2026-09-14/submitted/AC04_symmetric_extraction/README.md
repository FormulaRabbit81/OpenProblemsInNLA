# AC-04: Symmetric extraction and local rigidity

**Research continuation; not a solution of the exact-value problem.**

The new derived asymptotic-rank bound is

    3 <= asymptotic_rank(cw_2)
      <= (274 - 3*cuberoot(3025))^(1/4)
      < 3.896914.

The exact endpoint is certified between

    3.89691367400556951923
    3.89691367400556951924.

Neither asymptotic_rank(cw_2) = 3 nor asymptotic_rank(cw_2) > 3 is proved.

## Main construction

The report proves the symmetric degeneration

    P^n direct_sum cw_(4^n + 2^n - 2*3^n)
        <=deg D_(4^n) direct_sum cw_(2^n).

At power four it extracts cw_110 while padding with cw_16. An explicit
274-term border decomposition of the resulting direct sum is supplied;
after cancellation its tensor polynomial has degree at most nine.

The proof converts this into an asymptotic-rank bound using Strassen's
spectral duality and tight-three-tensor subrank theorem. The source cost
uses the standard q+2 border formula. The new argument does not assume that
asymptotic rank permits subtraction or that rank is additive on direct sums.

## Other results

The local fiber near the standard sixteen-term decomposition of P^2 has
two adaptive branches. A nearby ordinary three-mode formula is termwise
symmetric after rescaling. Consequently no fully supported rank-three
contraction exists in this neighborhood. This is not a global classification
of every sixteen-term decomposition.

For adaptive four-term expansion trees, a weighting with K nonzero leaves
and contraction rank s satisfies K <= s^2. The first-step optimization in
the report fixes the guaranteed extraction size K+u-2d; it does not cover
rank-sensitive improvements to that compression or other auxiliary tensors.

## Contents

- `report.pdf`, `report.tex`: sixteen-page mathematical report and editable source.
- `code/symmetric_extraction.py`: complete Laurent coefficient audits, direct
  border formulas, tight-support checks, and exact endpoint certificate.
- `code/verify.py`: local derivative blocks, mixed nonlinear obstruction,
  torus dimensions, rational adaptive example, support checks, and inherited bound audit.
- `code/exact.py`: exact arithmetic and rational linear algebra.
- `code/test_round4.py`: forty new regression/corruption tests.
- `code/run_all.py`: reproducible full check sequence.
- `results/`: exact JSON certificates and actual verification logs.
- `exploratory/search_far.py`: optional numerical multistart search; not a proof.
- `CLAIMS.md`: claim boundaries and proof locations.
- `sources.json`: source URLs and theorem locators.
- `prior/AC04_continuation/`: supplied prior package for provenance and inherited tests.
- `SHA256SUMS`: checksums for delivered files other than the checksum file itself.

## Reproduce

From this directory, with Python 3.10 or newer:

```sh
python code/run_all.py
```

The main checks use only the Python standard library. The recorded run also
included the optional inherited exact SymPy matrix audit:

```sh
python -m pip install sympy
python code/run_all.py --with-algebra
```

The recorded result is 40 new + 25 prior + 8 initial regression tests passing,
both new certificate programs passing, and the inherited matrix audit passing.
Do not use Python's `-O` option: inherited code uses assertions.

The optional numerical search requires NumPy and PyTorch. It is not invoked by
the main verifier. Its outputs are explicitly labeled exploratory. No numerical
optimizer result is used to establish a strict mathematical inequality.

To rebuild the PDF with a standard TeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Verification scope

Exact code verifies the finite algebraic premises and examples it states.
The all-power induction, analytic implicit-function argument, and imported
asymptotic theorems are written proofs, not proof-assistant formalizations.
No independent referee has reviewed the entire argument, and no research-priority
claim is made. The repository has not been edited or marked solved.
