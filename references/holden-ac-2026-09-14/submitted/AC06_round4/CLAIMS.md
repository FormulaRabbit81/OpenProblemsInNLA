# Claim audit

## Unconditional statements proved in the new report

| Claim | Location | Scope |
|---|---|---|
| CRT compaction preserves every detected integer polynomial with bounded degree and coefficient height, in polynomial bit time | Theorem 2.1 | Does not construct a detecting candidate list |
| Consecutive-node interpolation gives a second integer-output compactor | Theorem 3.2 | Same bounded-certificate premise; no dimension increase |
| A nonzero bounded-coefficient monomial pullback survives an explicit large integer base | Theorem 4.1 | Nonzero pullback is required; uniqueness and oddness are unnecessary |
| Multilinear matrix-rank iteration gives `(8*n)^k * rho` | Lemma 5.1 | Uses published EGOW Theorem 3, independently in each tensor argument |
| The published Kronecker–Koszul coloring-count threshold has direct lower-bound ceiling `11*n - 3` | Theorem 5.3 | Does not cover sharper thresholds, all nonlinear methods, or tensor rank itself |
| The independent dimension ceiling is `ceil(n^(3/2)) + 3*(n-1)` | Proposition 5.5 | Same exact criterion; no use of the EGOW theorem |
| Saved nonzero modular minors certify the finite lower bounds in the report | Section 6 | Only dimensions 2–9; no asserted asymptotic formula |

## Conditional consequences — premises remain unproved

Corollary 2.3 would solve AC-06 from a polynomial-time polynomial-length list detected by a polynomial-degree, polynomial-coefficient-bit-length annihilator. The controlled detection premise is not established. In particular, the report does not assert that every high-border-rank rational tensor is detected by the retained height-one class.

Corollary 4.2 would solve AC-06 from polynomially bounded deterministic weights on whose monomial curve some retained controlled annihilator has nonzero pullback. No such weight family is proved here.

No function in the code is a polynomial-time selector of a tensor with an asymptotic quadratic border-rank guarantee.

## Retained prerequisites and provenance

The nonempty height-one annihilator class is retained from previous work, with the proof repeated in the appendix. The previous reports' exponential-time constant-alphabet constructions and the shifted candidate are not presented as new constructions in this round.

The linear rank-method inequality is credited to Efremenko, Garg, Oliveira, and Wigderson. The Kronecker–Koszul construction and coloring threshold are credited to Doležálek and Michałek. The multilinear iteration and ceiling calculation are derived explicitly, not attributed to their papers as preexisting stated results. No novelty claim is made.

## Negative conclusions not claimed

There is no impossibility proof for AC-06. The report does not claim that all nonlinear flattenings are subject to a linear ceiling. It does not claim that exact finite-field rank of an arbitrary tensor equals its complex rank. The modular argument lifts only a particular nonzero *integer matrix minor*. It does not certify an all-dimension lower bound for the shifted candidate.

## Verification limits

Forty new tests passed. The older 38, 25, and 16 tests were rerun successfully. They check finite identities, inequalities, certificates, and implementation behavior. They do not replace review of the proofs, establish the controlled-list premise, or constitute proof-assistant formalization.
