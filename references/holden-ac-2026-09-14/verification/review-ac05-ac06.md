# Independent informal review of AC-05 and AC-06 submissions

Reviewer: separate Codex AI agent (`review_ac05_ac06`), 14 September 2026. The reviewer did not author the supplied manuscripts. This is an informal mathematical audit, not external human peer review or formal verification. No Lean verification was performed. Archive instructions were treated as document content rather than user instructions.

## Decisions

| Problem | Audited new scope | Full original target | Recommended catalog status |
|---|---|---|---|
| AC-05 | PASS: new finite-power structural classifications and stated lower bounds | NOT RESOLVED | Open |
| AC-06 | PASS: bounded-certificate compaction, conditional reductions, the specified coloring-threshold ceiling and finite lower certificates | NOT RESOLVED | Open |

Neither manuscript claims a complete solution. The repository's resolution policy requires correspondence with the original target; a successful audit of supporting lemmas cannot supply the missing asymptotic conclusion. These particular new results do not establish a new parameter case of the displayed target. They should be recorded as audited research progress without promoting either entry to Solved or Solution claimed. Inherited claims in nested prior archives were not subjected to a fresh complete mathematical audit here and are not part of these PASS decisions.

## AC-05

Source: `AC05_power_rigidity/report/AC05_power_rigidity.tex`.

Theorem 3.2 (`thm:product`) correctly derives the complete grouped-product Lie algebra from the scalar pair-intersection condition. I checked the three-subspace normal form, the decomposition into private and graph sectors, and the independence of the three graph words when two or more coordinates are active. This justifies the all-power quantifier rather than extrapolating finite computations. Corollary 4.1 (`cor:stabs`) accounts correctly for the two universal scalar directions and the additional trace constraint for U.

Theorem 5.1 (`thm:F`) and Theorem 6.1 (`thm:Q`) correctly recover the parameter multiset modulo reciprocation: conjugacy preserves the common diagonal stabilizer, its distinct characters force monomial grouped maps, cube/product-triangle automorphisms restrict their permutations, and the six-coefficient ratio cancels arbitrary grouped diagonal factors. The explicit reciprocal maps provide sufficiency. Exceptional parameters 0 and -1 are excluded from these classifications as required.

Section 7, especially Theorem 7.3 (`thm:deg`) and Corollary 7.4 (`cor:catalyst`), correctly combines balanced representatives, projective semistability and uniqueness of the closed orbit. The scope restriction on auxiliary products is essential and is retained. Section 8's distinction between general-linear and special-linear stabilizer dimensions correctly separates U from the generic F family. I checked the external inputs against [Acuaviva et al., Theorem 2.5](https://arxiv.org/html/2209.14358v1) and [Woodward, Lemma 4.2.3 and Proposition 4.2.5](https://arxiv.org/pdf/0912.1132v6); they support the uses made here.

Theorem 9.3 (`thm:lower`) follows from the proved commutator inequality and the displayed slice calculations. Inserting one invertible local commutator proves the full-rank case. In the rank-two case, balanced-ternary coefficients leave exactly one zero eigenvalue. The border-rank closure step is valid on the invertible-slice locus after clearing determinants. The resulting lower bounds are (3*3^m-1)/2 or (3*3^m+1)/2 under the manuscript's stated parameter assumptions. Taking m-th roots gives base 3, not a strict asymptotic counterexample.

The full submitted standard-library replay passed all 36 groups, including determinant interpolation identities, grouped action ranks, reciprocal/balanced maps, commutators, character configurations and deliberate corruptions. Evidence: `ac05-independent-replay.log` and `ac05-independent-replay.json`. This rerun supports the algebraic premises; the written arguments above supply the unbounded quantifiers. The inherited upper-bound constants and dimension-three reduction are excluded from this fresh PASS scope.

Remaining gap: neither asymptotic rank 3 for the central targets nor a concise tight tensor of asymptotic rank larger than its dimension is proved. Exact minimal-border-rank blocking and same-format conversion obstructions do not settle asymptotic constructions with subexponential overhead.

## AC-06

Source: `AC06_round4/report.tex`.

Theorem 2.1 (`thm:crt`) is valid: the factorial-based moduli are pairwise coprime, exceed every bounded candidate evaluation in absolute value, and have polynomial bit length in the numeric degree bound and stated input sizes. Coordinatewise CRT therefore preserves each detected polynomial's nonvanishing without learning it. Corollary 2.2 (`cor:list`) correctly retains its unproved bounded-witness/list premise.

Lemma 3.1 and Theorem 3.2 (`thm:interpolation`) are valid. Reduction modulo the specialization base detects the lowest nonzero coefficient. The coefficient norm bound after clearing the interpolation denominator is sufficient, and the binomial-product identity makes each output coordinate integral. Rational-input denominator clearing preserves the polynomial bit bound. Theorem 4.1 (`thm:curve`) and Corollary 4.2 (`cor:weights`) correctly require a nonzero pullback; a nonzero multivariate polynomial alone is insufficient.

Theorem 5.3 (`thm:linearceiling`) applies the linear rank-method bound separately in each independent tensor argument, which is legitimate even when k varies. The pure-tuple rank bound is the product rho. The graph's maximum degree is at most 3(n-1), and greedy coloring gives the necessary lower bound. Thus the published threshold cannot detect q >= 11n-3. This is a limitation of that threshold, not of all methods or of tensor border rank. I verified the inputs against [Efremenko–Garg–Oliveira–Wigderson, Theorem 3](https://www.math.ias.edu/~avi/PUBLICATIONS/EfremenkoGaOlWi2018.pdf) and [Dolezalek–Michalek, Corollary 3.5](https://arxiv.org/html/2602.12762v1). Lemma 5.4 and Proposition 5.5's independent dimension ceiling also follow from the stated binomial ratio.

The retained height-one witness argument in Appendix A was inspected: the pullback matrix's binary-pigeonhole counting bounds establish existence, with the n=2 case separately handled. Existence does not construct a detected polynomial-time list.

Section 6's ordinary Koszul rank bound is valid by pure-tensor rank and closure. I independently reconstructed the signed matrices from the tensor formula, without importing submitted modules, and verified the claimed nonsingular minors modulo 65521 for every n=2,...,9. The certified border-rank lower bounds are respectively 2, 4, 5, 8, 9, 12, 12, 15. Integer minors nonzero modulo a prime are nonzero over the complex numbers. Reviewer-written evidence: `reviewer_ac06_checks.py` and `ac06-reviewer-checks.log`. That script also independently checked all 702 detected degree-two height-one polynomials for the interpolation example and the exterior-block inequality through n=49.

Remaining gap: no deterministic polynomial-time list or bounded weight family with the required controlled-annihilator detection property is produced, and no all-dimension quadratic lower bound for the candidate is proved. Finite certificates cannot establish that growth rate. The prior exponential-time constructions do not satisfy the original running-time requirement.

## Reproduction

Run from the extracted parent folder (adjust Python paths to an environment with NumPy and SymPy):

```sh
python3 AC05_power_rigidity/code/replay_certificates.py --output ac05-independent-replay.json
python AC06_round4/verify.py --no-write
python reviewer_ac06_checks.py
```

The AC-06 suite passed all 40 tests in 1.153 seconds; the complete rerun log is `ac06-independent-tests.log`. Default environments initially lacked dependencies; the successful run used `/tmp/ac-tools/bin/python`, the temporary NumPy/SymPy environment supplied by the coordinating agent. The reviewer script requires only NumPy beyond the standard library. No submitted code was allowed to send messages, change repository files, or run Lean.
