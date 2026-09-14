# AC-06 — Fourth-round research package

**Status: PARTIAL RESEARCH. This is not a completed AC-06 solution.**

The required deterministic polynomial-time rational tensor family with a proved quadratic complex border-rank bound has not been obtained. This package proves polynomial-time *reductions*, a precisely scoped ceiling on one published threshold, and exact finite lower bounds for a retained candidate. It does not implement the missing tensor selector.

## Read first

`report.pdf` is the 13-page mathematical report. `report.tex` is its editable source. `CLAIMS.md` distinguishes proved statements from unfulfilled premises. `previous_work/AC06_round3_original.zip` is the byte-for-byte preserved third-round archive; its nested archives retain rounds two and one.

## Main results

**Certificate-preserving list compaction.** Given integer points and degree/coefficient-height bounds, either of two deterministic polynomial-time algorithms returns one integer point of the same dimension that preserves every bounded polynomial certificate detected anywhere in the list. Neither the polynomial nor a successful index is an input. This solves the *selection step conditional on a suitable short list*, not the construction of that list. A list containing a high-border-rank tensor does not by itself establish the required degree/height-controlled detection premise.

**Monomial-curve specialization.** If a bounded integer polynomial has a nonzero restriction to an explicitly weighted monomial curve, a sufficiently large explicitly specified integer base preserves nonvanishing. The preceding unique-minimum/odd-coefficient hypotheses are not needed. The relevant nonzero pullback at quadratic border rank is still unproved.

**A scoped all-power ceiling.** For the coloring-count threshold in Doležálek–Michałek, Corollary 3.5, the lower bound certified directly by that inequality is at most `11*n - 3`, independent of the tensor power and exterior-power pattern. An independent dimension argument sometimes improves the constant. This uses the published Efremenko–Garg–Oliveira–Wigderson linear rank-method theorem on each independent tensor argument. It is NOT a border-rank upper bound, NOT a barrier to all nonlinear methods, and NOT a barrier to sharper rank estimates for the same matrices.

**Finite exact certificates.** Nonzero Koszul minors modulo a prime certify lower bounds for the retained shifted family in dimensions 2 through 9. These do not prove quadratic growth.

## Reproduce

Use Python 3.10 or later; the recorded run used the versions in `evidence/environment.json`.

```bash
python -m pip install -r requirements.txt
python verify.py
python src/ac06_round4.py compact-demo --integer-output
python src/ac06_round4.py compact-demo
python src/ac06_round4.py curve-demo
python src/ac06_round4.py shifted-certificate 9
python src/ac06_round4.py ceiling 100
```

The new suite contains 40 test methods. It includes exhaustive small polynomial checks and independently recomputed determinants of the saved finite minors. The previous suites of 38, 25, and 16 tests were also rerun in extracted working copies; their logs are preserved.

The pure-Python compactors do not need NumPy or SymPy. NumPy is used for exact modular matrices, and SymPy for independent small symbolic regression checks. No floating-point tensor-rank optimization is used.

## Use the compactor on an explicit list

```python
from src.ac06_round4 import compact_crt

candidates = [[0, 0], [1, 0], [0, 1]]
result = compact_crt(candidates, degree=2, height=1)
merged_point = result["point"]
```

Here `degree` and `height` are bounds on potential integer polynomial certificates. The function does not verify that the input tensors have high border rank. It preserves a certificate **only when the certificate is nonzero on at least one supplied candidate**. Allocation guards protect the demonstration code from accidental enormous requests.

For rational candidates use `compact_rational` with `fractions.Fraction`, never floating-point approximations. `compact_list` is the second, interpolation-based integer-output implementation.

## PDF rebuild and verification

```bash
bash build_report.sh
```

An ordinary LaTeX installation with `pdflatex`, Latin Modern, AMS packages, `microtype`, and `hyperref` is required. The source includes the bibliography; no bibliography processor is needed. Building the report and running tests update the evidence logs, so an intentional rerun changes the corresponding integrity hashes.

The final PDF was rendered and visually inspected. The ZIP was tested and extracted for a clean test run. `SHA256SUMS.txt` hashes all delivered files except itself. These are integrity and regression checks, not independent mathematical review or proof-assistant verification.
