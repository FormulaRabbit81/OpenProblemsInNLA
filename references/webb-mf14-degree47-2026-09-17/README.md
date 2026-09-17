# MF-14: the exact seven-product closure degree is 47

**Author:** Marcus Webb, The University of Manchester.

**Date:** 17 September 2026.

**Outcome:** $`d_7=47`$ in the original complex full-closure model.

[Complete proof](proof.pdf) · [Standalone LaTeX](proof.tex) · [Retained canonical question](../../matrix-functions-and-stability/MF-14/README.md) · [Prepared PR text](PR_DRAFT.md)

Theorem 1 proves that every complex polynomial of degree at most 47 belongs to the Zariski closure of outputs computable from $`1,x`$ with at most seven products and free complex linear combinations, in the full coefficient space through degree 128. It also proves that the entire degree-at-most-48 space is not contained in that closure. Thus the exact maximum is 47, and the retained original equality $`d_7=42`$ is false.

The lower bound uses an explicit 49-parameter seven-product family. An exact Gaussian-rational contraction certificate proves the existence of a point whose coefficients below degree 47 vanish, whose degree-47 coefficient is one, and whose selected 48-by-48 coefficient Jacobian is invertible. The inverse function theorem and weighted input/output scaling then cover every degree-at-most-47 polynomial while making every coefficient of degrees 48 through 128 tend to zero. A self-contained generic dimension count, irreducibility and the polynomial $`x^{128}`$ give the matching upper bound.

The theorem concerns complex closure. It does not assert exact representation of every degree-47 polynomial, a real-coefficient analogue, or stable numerical coefficient recovery.

## Independent review and exact evidence

The [original final review](source/reviews/exact-degree47-final-review.md) audits the complete argument and binds it to the frozen [research proof](source/proof.md). Its author was a separate Codex agent from the agents that constructed the contact and supplied the certificate. The reviewer independently reconstructed all 129 coefficients and all 49 derivative columns using a reverse pass, and used a different, coarser Hessian bound. The exact residual, inverse defect and inverse norm agree with the author's forward-jet calculation.

The [contribution review](verification/packaging-review.md) checks the frozen-file preservation, standalone manuscript, original-target correspondence, and relocated reproduction. This packaging review is by the same independent reviewer as the final research review; it is not represented as a further independent mathematical referee. Separate agents prepared the LaTeX manuscript and the publication runner. The repository integrator separately checked the canonical entry, preservation, generated documents and required repository tests.

These are informal AI-agent reviews and exact computer-assisted checks, not external human peer review or proof-assistant verification. No Lean verification is claimed.

## Reproduction

Only Python's standard library is needed. From the repository root:

```sh
python3 -B references/webb-mf14-degree47-2026-09-17/verification/verify.py
python3 -B references/webb-mf14-degree47-2026-09-17/verification/test_verifier.py
```

The runner verifies the [frozen input manifest](verification/input_manifest.json), copies the ten inputs into a temporary directory, runs both exact checkers there, and compares their results with the preserved certificates. The author result must match byte-for-byte; the independent result must match every mathematical field and its full-array digest, with runtime metadata excluded. The runner also checks the exact contraction inequalities explicitly. The [verification guide](verification/README.md), [reproduction summary](verification/reproduction/summary.json), and [rejection-control log](verification/fail-closed-tests.log) describe the checks and their limits.

The original checkers use Python assertions. The publication runner therefore refuses optimized Python and launches its children with assertions enabled and Python environment options ignored. Use the runner above rather than invoking frozen programs with `-O`, `-OO` or `PYTHONOPTIMIZE`. The rejection controls verify that disabling assertions or altering frozen input is not silently accepted.

Numerical search, NumPy and high-precision Newton refinement are not required to reproduce the proof certificate. The [Gaussian-rational seed](source/experiments/lower_full49_seed.json) is the complete exact input. The [author certificate](source/experiments/lower_full49_certify.json) and [independent certificate](source/reviews/full49-degree47-fresh-check.json) are preserved unchanged from the research campaign.

From this contribution directory, rebuild the manuscript with:

```sh
mkdir -p /tmp/mf14-degree47-proof
xelatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/mf14-degree47-proof proof.tex
xelatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/mf14-degree47-proof proof.tex
```

The canonical entry is separately rendered with `python3 tools/render_problems.py MF-14` from the repository root. [Integration checks](integration-checks.md) record the local results.

## Source, attribution and preservation

This contribution follows the local MF-14 research campaign of 17 September 2026, developed with substantial ChatGPT/Codex assistance. The preserved `source/` files are byte-for-byte research artifacts; the standalone TeX manuscript is a typeset restatement, and the guarded publication runner is new. Their preservation and correspondence are audited separately. The frozen original target records the campaign's initial bounds and final disposition.

Marcus Webb's [earlier degree-44 contribution](../webb-mf14-degree44-2026-09-17/README.md), merged in [PR #287](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/287), already refuted the degree-42 equality. Matthew J. Colbrook retains credit for the [earlier degree-42 theorem](../colbrook-matrix-functions-2026-09-11/manuscripts/MF-14.pdf). Jarlebring and Lorentzon retain credit for the source conjecture and their general dimension theorem. The present proof's upper bound is self-contained; neither the earlier border constructions nor the external dimension theorem is required.

The campaign checked the primary source and relevant existing records on 17 September 2026; no exhaustive priority search is claimed. The original ID `MF-14`, canonical path, displayed conjecture, earlier archives and attribution are retained. `Solved` remains the canonical status, and the catalog's open count does not change. The unrelated auxiliary research and unsuccessful numerical searches are not needed in this contribution's proof package.
