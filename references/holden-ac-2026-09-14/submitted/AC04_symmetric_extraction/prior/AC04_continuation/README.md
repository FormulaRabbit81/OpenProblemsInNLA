# AC-04 continuation: adaptive contraction rigidity

**Status: AC-04 is not solved or disproved by this package.** The actual bound retained is

    3 <= asymptotic_rank(cw_2) < 3.923037967879.

That upper bound is inherited from the later supplied continuation and independently recertified here. It is not a numerical improvement in this round.

## Main results in this continuation

The report proves that every fully supported contraction of an adaptive four-term expansion tree of the nth power has rank at least 2^n. Formula choices and copy order may vary by branch. A block-matrix inverse-sum criterion describes equality. This extends the previous lower bound for fixed products of local decompositions.

For fixed product frames, it proves a complete equality classification: the weight tensor must itself factor, and each local weighted contraction must have rank two. For the standard four-term formula, there are exactly 2*3^n minimum sign patterns. Single-entry changes attain the next rank, 2^n+1.

A rational 16-term adaptive decomposition of the square attains contraction rank four with nonproduct weights. All 729 tensor coordinates are checked exactly. Thus the pure-weight conclusion must not be extended from fixed products to adaptive frames.

The report also constructs simultaneous two-slice degenerations, proves their formulas, and proves that their displayed seed inequalities admit the formal balanced value 3.95 for all parameters. This formal value is NOT a tensor asymptotic-rank lower bound.

## Read and reproduce

- `report.pdf`: 12-page mathematical report.
- `report.tex`: editable LaTeX source.
- `code/verify.py`: finite certificates using only Python's standard library.
- `code/test_verification.py`: 25 new regression/negative tests.
- `results/verification.json`: rational certificates and exact finite outputs.
- `prior/initial/`: the original supplied package, with caches removed.
- `prior/later_report.pdf`: the later supplied Library continuation.
- `exploratory/`: clearly separated numerical searches and modular tangent diagnostics; not proofs.

Python 3.10 or later is recommended. From the extracted package root:

```sh
python code/verify.py
python -m unittest discover -s code -p 'test_verification.py' -v
```

The recorded run passes all 25 new tests. The original eight tests and original exact SymPy matrix audit were also rerun; their outputs are in `results/inherited_*`.

To reproduce those inherited checks:

```sh
(cd prior/initial/code && python -m unittest -v test_certify.py)
python -m pip install sympy
python prior/initial/code/algebra_check.py --output results/inherited_algebra_rerun.json
```

To rebuild the PDF, run `pdflatex report.tex` twice. Required LaTeX packages are declared in the source. No separate font files are included.

## A conditional checkpoint, not a new bound

The report isolates a possible intermediate target: a 16-term decomposition of P^2 with a fully supported contraction of rank three. The adaptive-tree theorem excludes hierarchical four-term expansions from meeting it. If an unrestricted decomposition with those properties were found, the inherited speedup construction would imply asymptotic rank less than 3.918501. The corresponding scalar arithmetic is certified under `conditional_target` in the JSON.

**The required decomposition has not been supplied. The 3.918501 value is conditional and must not be reported as an achieved upper bound.** Even that improvement would not establish the exact value three.

## Verification boundaries

The all-power conclusions rely on the written proofs, not on enumerating large tensor powers. The sign-pattern modular ranks are combined with analytic upper bounds to identify their complex ranks. Modular ranks are not otherwise silently identified with characteristic-zero ranks.

The core certificate code uses integers and rational intervals for decisions. Floating-point experiments are separate and no numerical candidate from them is claimed as exact. No proof assistant or independent referee has verified the complete manuscript. No research-priority claim is made. The repository and the user's Library were not modified.
