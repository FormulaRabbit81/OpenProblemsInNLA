# MF-24: a counterexample to uniform polynomial norm comparison

**Author(s):** Georg Maierhofer  
**Affiliation:** University of Cambridge  
**Manuscript version:** 14 September 2026; independent review: 15 September 2026.

[Read the proof](proof.pdf) · [LaTeX source](proof.tex) · [Self-review](SELF_REVIEW.md) · [Verification record](verification.txt)

Theorem 1 constructs nonnegative nilpotent weighted shifts $`X_{m,t},Y_{m,t}`$ of order $`(m+1)^2`$. Their singular values agree after every complex scalar shift. For the same polynomial $`p_m(z)=\sum_{j=1}^m z^{(m+2)j}`$, the theorem gives

```math
\frac{\|p_m(X_{m,t})\|_2}{\|p_m(Y_{m,t})\|_2}
\ge \frac{\sqrt m}{1+(m-1)/t^2}
\qquad(m\ge2,\ t>1).
```

The finite choice $`t=m`$ makes this ratio at least $`(4/5)\sqrt m`$, disproving a bound uniform in dimension. Corollary 3 gives a lower bound of order $`N^{1/4}`$ for the optimal dimension-dependent constants. Their exact values and optimal growth are not determined.

## A small example

```python
from mf24 import norm_ratio, weighted_shift

X = weighted_shift(m=4, t=4.0, side="X")  # 25 by 25
Y = weighted_shift(m=4, t=4.0, side="Y")
print(norm_ratio(m=4, t=4.0))             # approximately 1.71276809
```

## Reproduce the checks

Tested with Python 3.13.5 and the versions in `requirements.txt`. From this directory:

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
python check_exact.py
OPENBLAS_NUM_THREADS=1 python check_numeric.py
```

`mf24.py` contains only the construction and polynomial-norm calculation. It generates one residue block at a time; a matrix of order $`(m+1)^2`$ requires SVDs of order at most $`m+1`$ for these polynomial norms.

`check_exact.py` checks polynomial identities (including fully symbolic complex shifts in small dimensions), compares independent constructions and verifies two rational norm certificates. `check_numeric.py` compares shifted singular values, checks dense matrix powers against the block formula and prints a norm-ratio table. Both reject a deliberately misplaced bridge. Finite computations support the proof; they do not prove its universal quantifiers.

To rebuild the manuscript:

```bash
pdflatex -halt-on-error proof.tex
pdflatex -halt-on-error proof.tex
```

Do not commit `.venv/`, `__pycache__/` or the auxiliary LaTeX files. Recheck any modified source before relying on the recorded results.

## Evidence and provenance

**Proposed catalog status: Solution claimed.** The construction, proof and code were developed and self-reviewed using ChatGPT. This is not an independent audit, external peer review or a publication-priority certificate. No complete Lean formalization is claimed or included. The original problem and earlier results remain credited in the manuscript and canonical entry.

## Independent informal review, 15 September 2026

A separate Codex AI assistant reviewed the complete manuscript and found no mathematical error. See [the audit](independent-review.md), [independently written checker](independent_check.py), and [its recorded results](independent-results.json). The original exact and numerical scripts were also rerun: [exact output](original-exact-rerun.txt), [numerical output](original-numeric-rerun.txt). This is informal AI-agent review, not external human peer review or formal verification. The proposed status remains Solution claimed pending maintainer assessment.

The earlier SELF_REVIEW.md and verification.txt remain historical records of the original package. Their statements about the absence of independent review refer to that earlier stage. The original verification.txt hashes the original README, before this attribution and review addendum; the proof, TeX and three original checking/construction scripts remain unchanged. Run `python3 independent_check.py --pdf proof.pdf` for the independent exact checks; add `--numeric` when NumPy is installed.

## Maintainer assessment, 15 September 2026

The [fresh maintainer audit of PR #264](../../reviews/2026-09-15-pr264/README.md)
accepts the complete negative resolution of MF-24's original uniform-boundedness
target. Its canonical status is now **Solved**. Exact dimension-dependent
constants and optimal growth remain open. The audit records separate proof
review, fresh exact/numerical checks and document review; it is informal AI
review, not external human peer review or Lean verification. The original
manuscript, checking scripts and historical reviews are preserved.

The stated Cambridge affiliation is supported by the
[current university profile](https://www.damtp.cam.ac.uk/user/gam37/).
