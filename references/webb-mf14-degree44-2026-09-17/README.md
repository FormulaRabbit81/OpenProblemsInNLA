# MF-14: degree-44 coverage and a negative resolution

**Author:** Marcus Webb, The University of Manchester.

**Date:** 17 September 2026.

**Outcome:** the canonical conjecture that the maximal covered degree is 42 is false.

[Read the complete proof](proof.pdf) · [Standalone LaTeX](proof.tex) · [Canonical MF-14](../../matrix-functions-and-stability/MF-14/README.md) · [Proposed PR text](PR_DRAFT.md)

Theorem 1 proves that every complex polynomial of degree at most 44 belongs to the Zariski closure of all seven-product outputs, taken in the full coefficient space through degree 128. Lemma 2 proves the simultaneous four-product border construction used by the remaining three products. Equation (19) records the nonsingular 45-by-45 Jacobian certificate. Corollary 3 uses Jarlebring–Lorentzon's published dimension theorem to give `44 <= d_7 <= 47`.

This is a complete negative answer to the retained equality `d_7 = 42`. The exact new maximum is undetermined. Exact representation of every polynomial, real Euclidean density and stable numerical coefficient recovery are not claimed. Matthew J. Colbrook retains credit for the [earlier degree-42 theorem](../colbrook-matrix-functions-2026-09-11/manuscripts/MF-14.pdf).

## Independent review

Two separate Codex agents conducted fresh mathematical and arithmetic reviews:

- [Border lemma review](verification/border-review.md): product count, product span, full differential minor, exact polynomial degeneration, all exceptional parameter choices, simultaneous closure and full ambient continuation. Its fresh verifier uses division-free sparse multivariate polynomial arithmetic.
- [Continuation and certificate review](verification/continuation-review.md): all 45 parameters, the derivative table, a new simultaneous-jet reconstruction, exact rational and modular determinants, closure transfer and the auxiliary upper bound. All 2,025 Jacobian entries agree with the separate interpolation check recovered from the chat.

Both reviews pass and bind their findings to the final proof source. The reviewers were separate from the assistant that developed the source conversation and from the agent that prepared this contribution. They could see the submitted argument and each worked independently on an assigned scope. This is informal AI-agent review, not external human peer review or formal proof-assistant verification. No Lean verification was performed.

## Reproduction

All three programs use only Python's standard library. From the repository root:

```bash
python3 -B references/webb-mf14-degree44-2026-09-17/verification/verify_border_independently.py
python3 -B references/webb-mf14-degree44-2026-09-17/verification/independent_degree44_jets.py
python3 -B references/webb-mf14-degree44-2026-09-17/verification/supplied_interpolation.py
```

Each program writes its certificate beside the script. Checks use explicit exceptions and also pass with `python3 -O -B`. The certificates contain the [border identities](verification/symbolic_certificate.json), [complete integer Jacobian](verification/independent-degree44-certificate.json), and [interpolation reconstruction and inverse modulo 3](verification/interpolation_certificate.json). The determinant is exactly 256; its residues modulo 3, 101 and 1009 are 1, 54 and 256. No polynomial in the variable `x` is truncated in the circuit or Jacobian computations. First-order jets discard only terms of second order in parameter increments, as required for differentiation.

The finite checks support the explicit algebraic identities and ranks. The proof's closure arguments require the mathematical review as well. See the [verification record](verification/checks.md) and [file hashes](verification/manifest.json).

The proof is standalone and can be rebuilt with XeLaTeX:

```bash
mkdir -p /tmp/mf14-proof-build
xelatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/mf14-proof-build references/webb-mf14-degree44-2026-09-17/proof.tex
xelatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/mf14-proof-build references/webb-mf14-degree44-2026-09-17/proof.tex
```

The resulting PDF is `/tmp/mf14-proof-build/proof.pdf`. The canonical entry is separately rendered by `python3 tools/render_problems.py MF-14`.

## Source and attribution

The user supplied [this ChatGPT conversation](https://chatgpt.com/share/6aaba6d9-3424-83eb-b278-21e3b917a83b) and explicitly requested the author credit “Marcus Webb, The University of Manchester.” The construction and its earlier checks were developed with substantial ChatGPT assistance. The chat's earlier “independent-method” validation was performed by the same assistant and is not counted as an independent referee review here.

The [degree-44 construction](source/degree44-construction.md) and [same-assistant validation](source/same-assistant-validation.md) are unchanged text extracts from the shared conversation. Their original sandbox attachment links and citation tokens are retained as historical source text; the attachments themselves were not retrievable through the shared page. [Provenance metadata](source/provenance.json) records the source URL, retrieval date and hashes. The interpolation program was recovered from code exposed in the conversation and inspected before execution. The new proof is a standalone reconstruction of the supplied argument using its polynomial-determinant formulation, supplemented with explicit cofactor formulas from the fresh review. It is not represented as a byte-for-byte copy of the unavailable original PDF or TeX attachment.

Jarlebring and Lorentzon retain credit for the original conjecture and the dimension theorem. The primary source's Theorem 10 and Conjecture 13 were checked on 17 September 2026. A limited title/degree-44 search found no additional relevant resolution; no exhaustive priority search is claimed.

## Repository preservation

The original problem statement, ID `MF-14`, canonical path and ID registry are unchanged. The earlier submission and its certificates are retained untouched. The canonical status becomes `Solved`, with the negative outcome and actual review level stated explicitly. MF-14 leaves the open count; the exact optimum is described as a further question without replacing the permanent target or assigning a new ID.
