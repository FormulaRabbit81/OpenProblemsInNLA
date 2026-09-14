# AC-02 — Exact certificates and a component obstruction

**Status: partial research; the original exact-rank problem is not solved.**

This archive does not determine the exact complex bilinear rank of 3 x 3
matrix multiplication. It supplies neither a 22-product identity nor a global
lower bound of 23. The established general interval remains 19 <= rank <= 23.
The PDF's bibliography identifies the source of the imported lower bound;
the 23-product upper bounds are verified here exactly from attributed data.

## Read first

`report/AC02_report.pdf` is the 17-page mathematical report. Its LaTeX source and
the two included formula fragments are in the same directory.

The main computer-assisted theorem is that the complete fixed-support variety
for the included Laderman decomposition is a 58-dimensional algebraic torus.
Its closure under the standard GL(3,C)^3 action is the unique 76-dimensional
irreducible component of the 23-slot coefficient variety through the baseline
point. Every ordered slot has contraction signature 1 or 2 throughout that
component; no point on it has a zero slot. This is not a classification of all
components, and it does not imply the global lower bound 23.

Other exact results are support-wide factor nonvanishing and pairwise
Khatri–Rao independence for the supplied Laderman and Sun schemes, an explicit
six-parameter slice after 52 elementary rescalings, and general matrix-rank-sum
constraints. In particular, a hypothetical output-tight 22-product scheme must
have five rank-two outputs and seventeen rank-one outputs. Output-tightness
is an extra hypothesis, not established for arbitrary 22-product schemes.

## Quick verification

Tested environment: Python 3.13.5, NumPy 2.3.5, SymPy 1.14.0. The exact replay
checker needs NumPy; regeneration additionally needs SymPy. The stand-alone
rational-complex identity checker needs only the Python standard library.

From this directory:

```sh
python -m pip install -r requirements-check.txt
python code/verify.py
python code/self_tests.py
python code/verify_candidate.py data/laderman23.json
python code/verify_candidate.py data/sun23.json
```

Do not run `verify.py` or the regression tests with `python -O`: assertions are
part of the checking. `verify.py` explicitly refuses optimized execution.
On success it writes `results/exact_verification.json` with
`certificate_status: PASS` and `global_exact_rank_determined: false`.

The generator is not imported by the checker. They share indexing and
matrix-building helpers, so this is a replay architecture, not independent
mathematical authorship or a formal verification claim. A separate
standard-library checker uses six matrix indices directly. The written
algebraic-geometric argument in the PDF still requires mathematical review.

## Regenerate the certificates

```sh
python -m pip install -r requirements-generate.txt
python code/build_data.py
python code/generate_certificates.py
python code/verify.py
```

The generator emits small finite certificates rather than a trusted numerical
answer: integer inverse matrices, integer lattice combinations, nonvanishing
traces, triangular pivot patterns, and selected integer minors certified
nonzero modulo 1000003. The checker replays their exact identities.

## Instantiate the family

```sh
python code/instantiate_family.py --parameters 2 3 5 7 11 13 \
  --output results/example.json
python code/verify_candidate.py results/example.json
```

By default this uses the six-parameter elementary-gauge slice. `--full` uses
all 58 free parameters. Every parameter must be a nonzero rational number.
The generated identity is checked before saving. The displayed sample is
already included as `data/laderman_six_parameter_example.json`.

`data/laderman_six_parameter_exponents.csv` gives a human-readable formula for
each allowed coefficient: multiply the baseline sign by z1^e1 ... z6^e6.
Its slot, row and column labels are explicitly **1-based**; JSON certificate
labels and factor arrays are **0-based**. All matrix vectorizations are
row-major. The proof is valid for arbitrary nonzero complex parameters;
rational parameters are used only for concrete exact sample files.

The stand-alone checker accepts integers, rational strings such as `"2/3"`,
and Gaussian-rational entries such as `{"re":"2/3","im":"-1/7"}`. Floating
point entries are rejected. A successful identity check proves an upper
bound using the number of nonzero slots, not optimality.

## Numerical exploration, not proof

```sh
OPENBLAS_NUM_THREADS=1 python code/search_rank22.py \
  --sweeps 500 --polish-steps 30 --random-starts 8 --seed 20260914
```

The recorded run used 54 unrestricted-coefficient starts. The best residual
norm was 0.16307567682559754, not zero. No exact rank-22 identity was found.
Failure to converge is **not** a lower bound. Small residuals would not be
exact identities either. Settings, progress and coefficient magnitudes are
recorded in `results/numerical_rank22_search.json`; the best approximate
factors are in `results/numerical_best_rank22.npz`. The numerical run is not
used in any theorem. Re-running it overwrites those exploration results.

## What is and is not in this archive

- `report/`: full written proofs, mathematical scope and bibliography.
- `code/`: data reconstruction, certificate generation/replay, regression
  tests, rational-complex candidate verification and numerical exploration.
- `data/`: two existing algorithms and an exact rational family instance.
- `proofs/`: finite exact certificates for the restricted results.
- `results/`: successful exact-check reports and clearly labeled numerical logs.

`SOURCES.md` records the primary-source provenance and model distinctions.
`AUDIT.md` identifies proof dependencies and remaining global gaps.
`environment.json` records tested versions; `MANIFEST.sha256` records package
integrity. On systems providing sha256sum, run `sha256sum -c MANIFEST.sha256`.

No repository files were modified. No Lean proof, external peer review,
independent referee audit, full solution, or novelty priority is asserted.
Algorithm attribution is in the data and in `ATTRIBUTION.md`.

## Rebuild the report

With a LaTeX installation containing the packages named in the preamble:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error AC02_report.tex
pdflatex -interaction=nonstopmode -halt-on-error AC02_report.tex
```

The distributed PDF has been rendered and visually checked. Bibliography
links are live source locators, not promises that future versions will be
unchanged; versioned arXiv identifiers are supplied wherever used.
