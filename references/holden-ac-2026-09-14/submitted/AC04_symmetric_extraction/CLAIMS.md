# Claim ledger

## Actual asymptotic-rank result

**Theorem 4.2.** Over C,

    3 <= asymptotic_rank(cw_2)
      <= (274 - 3*cuberoot(3025))^(1/4) < 3.896914.

Dependencies: Theorem 3.1 (explicit symmetric extraction), the standard CW
border-rank formula, Strassen spectral duality, and Strassen tight-three-tensor
subrank formula applied in Lemma 4.1. The strict decimal sign is certified with
integer/rational arithmetic in `results/symmetric_extraction.json`.

This improves the supplied 3.923037967879 bound. The old bound is rechecked only
for provenance; it is not the numerical result of this continuation.

## New exact constructions and structural results

| Result | Location | Scope |
|---|---|---|
| P^n + cw_t degenerates from D_r + cw_s | Theorem 3.1 | r=4^n, s=2^n, t=r+s-2*3^n, every n>=1 |
| Explicit r+s+2-term border formula | Section 3.4 | Direct sum; tensor error polynomial degree at most 9 |
| Power four best in the evaluated uniterated family | Proposition 4.3 | Uses exactly the source cost s+2 and auxiliary subrank bound |
| Nearby symmetric outputs are termwise symmetric | Theorem 5.1 | Analytic neighborhood of the standard ordered product tuple, every n |
| Exactly two local symmetric decomposition branches | Theorem 6.1 | Second power, reduced analytic fiber germ at the standard tuple |
| No nearby fully supported rank-three contraction | Corollary 6.2 | Ordinary sixteen-term decompositions in that neighborhood |
| Two closed components through the standard point | Section 6.5 | Does not classify remote components |
| K <= s^2 for adaptive weighted contractions | Theorem 7.1 | Arbitrary zero weights; full-spark adaptive expansion trees |
| Full support best for the canonical first-step estimate | Section 7.1 | Guaranteed size K+u-2d only, not sharper rank-sensitive compression |
| Rational adaptive example, rank-four contraction | Section 8.1 | All 729 coefficients exact; weight-array rank four |

## Not established

- The equality asymptotic_rank(cw_2) = 3.
- Its negation, or any asymptotic-rank lower bound larger than three.
- Equality of the actual asymptotic rank with the new upper endpoint.
- An ordinary-rank bound R(P^4) <= 274 - 3*cuberoot(3025).
- A global exclusion of sixteen-term decompositions with rank-three contractions.
- Global optimality of the new degeneration method.
- Any exact nonexistence result inferred from the 24 numerical search failures.

The prior conditional target 3.918501 is now weaker than the actual new bound.
Its hypothetical rank-three-contraction decomposition was not found and is not
needed to establish the new 3.896914 bound.

## Verification record

`results/run_all.json` records a successful actual run of both new certificate
programs, 40 new tests, 25 prior tests, 8 initial tests, and the optional inherited
SymPy matrix audit. General theorems still require their written proofs and the
cited external results. No proof assistant or independent peer review is claimed.
