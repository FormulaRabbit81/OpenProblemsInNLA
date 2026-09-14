# Primary sources checked

Public pages were read through the website; no GitHub connector was used. Access date: September 14, 2026.

1. **Open Problems in Numerical Linear Algebra, AC-06.**
   https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/arithmetic-and-complexity/AC-06/README.md
   Exact target: deterministic polynomial time in n, binary rational output, complex border rank at least c*n^2 for all sufficiently large n. Repository last-check date: September 10, 2026. Its status field reads Open. That metadata is not used as an argument that the problem cannot be solved.

2. **Kumar and Volk, A Polynomial Degree Bound on Equations for Non-Rigid Matrices and Small Linear Circuits.** ITCS 2021, Article 9.
   https://doi.org/10.4230/LIPIcs.ITCS.2021.9
   https://benleevo.lk/pdf/degbound.pdf
   Used for context on the established polynomial-annihilator framework. The exact retained height-one bound used by the new reductions is proved in the report's appendix.

3. **Doležálek and Michałek, Nonlinear methods for tensors: determinantal equations for secant varieties beyond cactus.** arXiv:2602.12762v1, February 13, 2026.
   https://arxiv.org/html/2602.12762v1
   https://arxiv.org/pdf/2602.12762
   Section 3, Theorem 3.3 and Corollary 3.5 were checked against rendered PDF pages 5–6. The report uses the precise coloring-count threshold and pure-tuple exterior-factor count. Examples 3.6–3.7 explicitly show the threshold need not be tight. The new ceiling is NOT attributed to this paper as a stated theorem.

4. **Efremenko, Garg, Oliveira, and Wigderson, Barriers for Rank Methods in Arithmetic Complexity.** ITCS 2018, Article 1.
   https://doi.org/10.4230/LIPIcs.ITCS.2018.1
   https://www.math.ias.edu/~avi/PUBLICATIONS/EfremenkoGaOlWi2018.pdf
   Theorem 3, rendered PDF pages 10–11: for a linear tensor-to-matrix map bounded by rho on pure 3-tensors, all outputs have matrix rank at most 8*n*rho. Complex numbers meet the field hypothesis. The new report applies this theorem successively to the independent arguments of a multilinear lift; it does not falsely apply it directly to a nonlinear diagonal map.

5. **Mańdziuk, Border rank lower bounds beyond weak border apolarity.** arXiv:2609.12121v1, September 10, 2026.
   https://arxiv.org/abs/2609.12121
   https://arxiv.org/html/2609.12121v1
   Checked as recent primary-source context. It supplies methods and particular lower-bound examples, not the qualifying family constructed in this package. None of the new theorems depends on its technical results.

6. **Narayanan, Arithmetic circuit lower bounds from sumset expansion.** arXiv:2607.15848v1, July 17, 2026.
   https://arxiv.org/html/2607.15848v1
   Checked the distinction between semi-explicit number-field output and AC-06's rational encoding. Not used as a proof ingredient in the new report.

The third-round report is an attached working manuscript, not independent validation. Its original bytes and nested earlier archives are preserved. The current check did not supply the missing controlled-list or controlled-curve theorem; this search outcome is not a proof that no qualifying result exists.
