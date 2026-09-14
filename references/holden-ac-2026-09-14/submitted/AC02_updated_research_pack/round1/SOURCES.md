# Source provenance and model audit

The main report contains inline numbered references for literature claims.
Public source locators and the particular versions inspected are recorded
below. The original mathematical derivations and finite certificates are
not attributed to these papers unless explicitly stated.

## Original target and contribution rules

AC-02, exact complex bilinear rank:
https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/arithmetic-and-complexity/AC-02

Canonical raw statement read:
https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/arithmetic-and-complexity/AC-02/README.md

The entry is marked Open and last checked 2026-09-10. Its coefficients are
arbitrary complex numbers. It explicitly distinguishes separated bilinear
factors from algorithms that mix both inputs inside a factor.

Contribution requirements:
https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/CONTRIBUTING.md

A restricted theorem, self-check or finite-field result does not by itself
resolve the full target. Nothing in this archive should be presented as a
solved or Lean-verified AC-02 submission.

## Existing bounds and exact algorithms

Markus Bläser, *Fast Matrix Multiplication*, Theory of Computing Library,
Graduate Surveys 5 (2013), 1–60; Introduction and Example 5.10.
DOI 10.4086/toc.gs.2013.005.
https://theoryofcomputing.org/articles/gs005/gs005.pdf

Source used for the imported 19 <= R_C(M3) <= 23 interval. The original
lower-bound paper is Bläser, *On the complexity of the multiplication of
matrices of small formats*, J. Complexity 19(1), 43–60 (2003),
DOI 10.1016/S0885-064X(02)00007-9. This report does not reproduce its proof.

Julian D. Laderman, *A noncommutative algorithm for multiplying 3 x 3 matrices
using 23 multiplications*, Bull. AMS 82 (1976), 126–128.
DOI 10.1090/S0002-9904-1976-13988-2.
The original publisher PDF was not accessible in this session. The displayed
standard formulas were reconstructed and all 729 identities checked. They
are attributed to Laderman, not claimed as a new algorithm.

Yinqi Sun, *An Exact 56-Addition, Rank-23 Scheme for General 3 x 3 Matrix
Multiplication*, arXiv:2604.27645v1, Section 5.
https://arxiv.org/html/2604.27645v1
The expanded factors were transcribed, converted to row-major U,V,W arrays
and verified exactly. This work uses the decomposition only; it neither
optimizes nor independently claims an optimal addition count. The source is
marked CC BY 4.0. It traces its decomposition to an earlier scheme under a
cyclic tensor reorientation; Sun's data name identifies the presentation
used, not a claim of original authorship for the underlying tensor orbit.

Chengu Wang, *Automated Lower Bounds for Bilinear Complexity over Finite
Fields*, arXiv:2603.07280v11, 29 August 2026.
https://arxiv.org/html/2603.07280v11
Its 3 x 3 lower-bound improvement is over F_2, not C.

Josh Alman and Baitian Li, *Asymptotic Rank Speedup Theorems, Revisited*,
arXiv:2605.21738v1, Introduction.
https://arxiv.org/html/2605.21738v1
Distinguishes exact, border and asymptotic rank and identifies the small
3 x 3 exact-rank and border-rank questions as unresolved.

## Geometry, invariants, and parameter families

Petr Tichavský, *Characterization of Decomposition of Matrix Multiplication
Tensors*, arXiv:2104.05323v1, Section IV and Proposition 2.
https://arxiv.org/html/2104.05323v1
Contraction signatures and their invariance under standard basis changes are
existing concepts. The report proves the invariance directly in its chosen
U,V,W (untransposed output) convention and checks constant signatures on its
entire explicit torus.

Xin Li, Yixin Bao and Liping Zhang, *On the local dimensions of solutions of
Brent equations*, arXiv:2303.09754v2.
https://arxiv.org/html/2303.09754v2
Prior work on Jacobian-rank and orbit-dimension arguments. In particular, a
Jacobian nullity is an upper bound, not by itself an attained local dimension;
possible nonradicality must not be silently ignored.

Marijn J. H. Heule, Manuel Kauers and Martina Seidl, *New ways to multiply
3 x 3-matrices*, arXiv:1905.10192v1, Section 7.
https://arxiv.org/html/1905.10192v1
Their parameter-introduction procedure is a specified iterative linear
heuristic. Reporting zero introduced parameters for Laderman is not a proof
that all coupled nonlinear deformations are trivial. This archive does not
claim priority for its family or component calculations.

## Historical claim screened but not used as a resolution

Rodney W. Johnson and Aileen M. McLoughlin, *Noncommutative Bilinear Algorithms
for 3 x 3 Matrix Multiplication*, SIAM J. Comput. 15(2), 595–603 (1986),
DOI 10.1137/0215043.
https://vigo.ime.unicamp.br/mt404/johnson1986.pdf

The first page mentions an indication of a possible complex 22-product
algorithm from unpublished work. Its reference [12] is a private
communication, not a displayed construction. The first and last pages were
visually inspected. No 22-slot exact certificate was obtained from this
remark, and it is not treated as evidence that AC-02 has been solved. The
paper's actual displayed algorithms have 23 products.

No full third-party paper is redistributed in this archive.
