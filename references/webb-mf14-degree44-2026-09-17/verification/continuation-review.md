# Independent MF-14 degree-44 continuation review

Reviewer: separate Codex agent `/root/review_existing_mf14`, 2026-09-17.

## Verdict and scope

**PASS for the continuation, exact Jacobian certificate, closure transfer,
and optional upper bound.** This review assumes the simultaneous four-product
border-availability lemma, assigned separately to another reviewer. Combined
with that lemma, the reviewed argument proves that the canonical equality
`d_7=42` is false: in fact `44 <= d_7 <= 47`.

Reviewed the recovered user-supplied chat excerpts archived as
`source/degree44-construction.md` and `source/same-assistant-validation.md`,
the recovered code at `verification/supplied_interpolation.py`, the canonical
repository MF-14 statement, and the primary Jarlebring--Lorentzon paper
linked below. No repository files were edited by this reviewer.

This is an independent agent review, not external human referee approval or
formal proof-assistant certification.

## Circuit and parameter count

The coefficient map is transcribed correctly from the chat. There are
`2+7+4+3+5+3+6+6+9 = 45` free scalar parameters. The two shape parameters give
`Q=x^4+alpha*x^3` and `R=x^5+beta*x^3`. Seven coefficients of the monic degree-12
polynomial `P` vary in degrees `3,6,7,8,9,10,11`. The three continuation
products have degrees at most `17,22,44` for every parameter choice, because
their operands have degrees at most `(12,5)`, `(17,5)` and `(22,22)`.
The nine output coefficients represent a free linear combination. Thus
`Phi: C^45 -> C[x]_(<=44)` is a polynomial map with integer coefficients.

At the displayed zero-one point, independently obtained:

```text
Q = x^4+x^3
R = x^5
P = x^12
F = x^17
G = x^22+x^19
H = G*(G+Q+P+F).
```

## Independent exact computation

Wrote `independent_degree44_jets.py` from the defining circuit. It imports
neither a prior verifier nor a stored matrix. It represents polynomials in x
and 45 first-order parameter increments as a sparse dictionary. Only products
of two parameter increments are discarded; all powers of x are retained.
Thus the integer output coefficients and all 45 derivative columns are
computed simultaneously.

Separately derived all columns by the chain rule. At the certificate point,
put `B=R+x^2`, `K=2G+Q+P+F`, and `L=K*B+G`. The columns, in stated order, are

```text
alpha: G*x^3
beta:  (L*P+K*F)*x^3
xi_j:  (L*R+G)*x^j, j=3,6,7,8,9,10,11
u:     L*R times (x,x^2,Q,R)
v:     L*P times (x,x^2,Q)
a:     K*B times (x,x^2,Q,R,P)
b:     K*F times (x,x^2,Q)
c:     (G+Q+P+F) times (x,x^2,Q,R,P,F)
d:     G times (x,x^2,Q,R,P,F)
z:     (1,x,x^2,Q,R,P,F,G,H).
```

These agree in all 2,025 entries with the simultaneous-jet matrix. Ordinary
Gaussian elimination over exact rational numbers gives determinant **256**.
A separate modular elimination yields residues **1 modulo 3**, **54 modulo
101**, and **256 modulo 1009**. Every matrix entry is between zero and six.

Only after completing that calculation, extracted and ran the supplied
interpolation verifier recovered from the conversation (archived as
`verification/supplied_interpolation.py`). Its circuit transcription and
degree-13 parameter bound are correct: coefficient parameter degrees are at
most 1 for Q/R/P, 4 for F, 6 for G, 12 for H, and 13 for the final output.
Its differentiation weights are checked on the monomial basis through degree
13, so the interpolation is exact. Its reconstructed matrix agrees entrywise
with mine, as do its parameter order, point and determinant.

All checks use explicit exceptions and passed with `python3 -O`. The full
independently computed integer matrix, pivot sequence, row swaps, residues and
script SHA-256 are in `independent-degree44-certificate.json`.

## Joint availability and full ambient closure

Let A4 denote quadruples jointly available after at most four products and
B4 its Zariski closure in `(C[x]_(<=16))^4`. For each fixed setting of the
continuation scalars, the remaining three products define a polynomial map T
on this entire ambient quadruple space. An arbitrary degree-at-most-16 input
quadruple gives product degrees at most `32,48,96`; thus T has codomain
`C[x]_(<=128)` without any coefficient truncation.

For an actually available quadruple, the same continuation uses at most three
additional products. Therefore `T(A4)` is contained in P7. If Y is the
Zariski closure of `T(A4)`, then `T^(-1)(Y)` is closed and contains A4. Hence
it contains B4, proving `T(B4) subset Y subset X7`. This implication does not
require T to be a closed map, and it does not assume separate availability
implies joint availability.

The simultaneous border lemma places every proposed starting quadruple in
B4, so every value of Phi belongs to X7. The exact nonsingular Jacobian gives
a Euclidean-open subset in the image by the complex inverse function theorem,
and therefore gives Zariski density in the degree-44 coefficient subspace.
Since X7 is closed, it contains that whole subspace. No approximating output
is projected or truncated; coefficients above degree 44 vanish in the limit.

This resolves the retained canonical yes/no equality negatively. It does not
identify the exact new maximum, prove exact representation of every degree-44
polynomial, assert a practical stable algorithm, or establish real Euclidean
density.

## Optional upper bound

Checked the primary source
[Jarlebring--Lorentzon, arXiv:2504.01500v3](https://arxiv.org/html/2504.01500v3),
Theorem 10 (HTML equation 68): for `m>2` its polynomial set has dimension
`m^2`. Sections 2.1--2.2 identify the set as the image of the universal
polynomial circuit map and use complex Zariski closure. Conjecture 13 is
precisely the equality refuted here. I checked applicability rather than
independently reproving their dimension theorem.

For seven products, all finite circuits can be compressed into a universal
polynomial map from affine 79-space: 70 operand coefficients and nine output
coefficients. Unused multiplication slots can be padded with zero products.
Its image is P7, hence its image closure X7 is irreducible. The cited theorem
gives `dim X7=49`.

If the closed subspace `C[x]_(<=48)` lay in X7, it would be a closed subset of
the same dimension 49. Irreducibility forces equality. Seven successive
squarings produce `x^128`, which lies in X7 but not in that subspace, a
contradiction. Nestedness excludes every larger degree as well. Consequently
`d7 <=47`, giving `44 <= d7 <=47` once the lower theorem is established.
The lower theorem itself is independent of this published dimension input.

## Reproduction

```bash
python3 -O references/webb-mf14-degree44-2026-09-17/verification/independent_degree44_jets.py
python3 -O references/webb-mf14-degree44-2026-09-17/verification/supplied_interpolation.py
```

The first writes `independent-degree44-certificate.json`; the second writes
`interpolation_certificate.json`. Their complete run outputs and the
cross-method comparison are stored alongside this review.

## Standalone manuscript audit — 2026-09-17

Read the standalone exposition at
`references/webb-mf14-degree44-2026-09-17/proof.tex`, including its model,
continuation section, displayed parameter point, complete derivative table,
full ambient closure transfer, determinant conclusion and upper-bound
corollary. Every circuit, parameter ordering and derivative-table formula
matches the independently recomputed certificate above. The final
continuation and upper-bound arguments are correct and retain the same
scope as this review. No mathematical correction to those sections was
needed. The border lemma remains covered by the separate reviewer.

### Final source binding — 2026-09-17

Re-read the final frozen manuscript, including the continuation, derivative
table and upper bound. The added border-algebra appendix does not change
these reviewed arguments; the appendix identities fall within the separate
border review. The verdict above applies to the final `proof.tex` whose
SHA-256 over its exact file bytes is:

`c987a6ac3532b50a8241702612c05d951d2a7d9b467a14aec922ea3c83d3de88`

Also compared the bundled independent continuation verifier against my
reviewed original. Its only change prints the certificate basename rather
than its absolute path, avoiding a personal machine path in the published
log. Its mathematical code and checks are unchanged.
