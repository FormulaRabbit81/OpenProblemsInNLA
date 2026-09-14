# AC-03: pair-space reduction and cubic obstructions

**Verified partial research, not a complete solution of AC-03.** The exact complex
border rank of 3 x 3 matrix multiplication is not determined here. The numerical
interval remains **17 <= border rank(M3) <= 20**. Those endpoints are inherited,
published results, not new bounds from this package.

Start with `report.pdf` (editable source: `report.tex`).

## Principal results

The audited previous classification implies a smaller equivalent target: a
17 x 9 x 9 inclusion tensor `F_E` with 35 nonzero unit coordinates. The condition
`border rank(F_E) = 17` is equivalent to `border rank(M3) = 17`.

The report proves that the rank-one scheme section of its matrix plane is the
reduced 2 x 4 Segre variety. Consequently `cactus rank(F_E) >= 18`. This is **not**
a border-rank lower bound. An explicit, different 17 x 9 x 9 control tensor has
border rank 17 and cactus rank at least 18.

For the prior four-factor target `Q`, all three versions obtained by grouping two
of A, B, C while keeping D separate have border rank exactly 17. Exact Fourier
formulas and complete coefficient expansions are supplied. Their grouped terms
do not split into four-factor rank-one terms.

A 154,350-column integer exterior-contraction map rules out normalized cubic-pole
constructions at all 24 normalized 17th-root configurations with 16 independent
base products. A second exact certificate excludes the 2 x 4 x 2 grid plus its
barycenter. Its proof checks a complete 135-dimensional rational kernel, necessary
quadratic relations, and a final rank-nine versus rank-three contradiction.
These results do not exclude arbitrary base configurations or higher poles.

A separate exhaustive calculation excludes all 24 character patterns of a
restricted single-character monomial Fourier ansatz for the pair plane. The two
24-pattern enumerations are different mathematical classifications.

## Verification

Python 3.13.5 and SymPy 1.14.0 were used. New certificates use only the standard
library; SymPy is used by the retained prior audits.

```bash
python code/check_manifest.py
python -m pip install -r requirements.txt
python code/verify_all.py
```

Do not use Python's `-O` option; assertions are proof checks. The combined verifier
rejects optimized mode. It regenerates every exact result, runs eight consistency
tests, checks two cyclic configurations independently modulo 103, and reruns the
unchanged prior archive (including the original lower/upper-bound checks).

`python code/verify_all.py --skip-prior` checks only this round's certificates.
It does **not** revalidate the inherited enumeration or numerical endpoints.

`results/full_run_summary.json` records the full run. The delivered manifest
hashes describe the delivered files: verify it **before** recomputation, because
running the verifier updates results and timestamps.

## Mathematical dependencies and boundaries

`prior/AC03_round2_research_package.zip` is retained byte for byte. Its report and
exhaustive Borel classification are dependencies of the single-pair equivalence.
The present report gives the additional logical reduction explicitly; it does
not replace the inherited enumeration by a symmetry assumption.

The ordinary rank, border rank, cactus rank, and grouped border ranks are kept
separate throughout. The grouped certificates are not a decomposition of M3 or
an ungrouped decomposition of Q. The grid and cyclic statements refer to scalar
pole order after all factor curves have nonzero holomorphic limits.

`research/` contains exploratory records. Parameter-incomplete enumerations,
finite-field samples, and optimizer failures there are not used to prove
nonexistence over the complex numbers. See `research/README.md`.

## Completion criterion

A genuine 17-term degeneration of F_E would solve AC-03 at 17. A universal
nonmembership proof for its pair plane would improve the lower bound to 18,
which would still not determine whether the exact answer is 18, 19, or 20.
Neither is supplied here.

All public mathematical sources and the exact role of each are listed in the
report. The work is computer-assisted verification, not a proof-assistant
formalization, independent peer review, or a claim of established novelty.
