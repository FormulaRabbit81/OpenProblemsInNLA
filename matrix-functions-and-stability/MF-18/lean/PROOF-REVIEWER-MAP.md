# MF-18 implementation and proof map

This is author-prepared navigation for the exact local340 source snapshot.
The separately sealed independent review reports determine source-review scope.
[IMPLEMENTATION-MAP.json](IMPLEMENTATION-MAP.json) supplies the exact file,
declaration, line and header hash for every contract and every source hash in
the complete 38-module closure. No claim here replaces the actual local340
receipt or the pending Linux Comparator check.

## Concrete statement semantics

`Mat n` is `Matrix (Fin n) (Fin n) ℂ`. `GreenAssumptions` contains only the
original assumptions: Hermitian $R,P$, positivity on the entire unit circle,
a stabilizing nonsingular solution for every $\eta>0$, its finite nonsingular
right limit, regularity of the determinant polynomial, and algebraic simplicity
of its unit-circle roots. The canonical theorem adds the original uniqueness
premise and the equation saying that the circle root count is $2m$.

`regularizedB = Cᴴ + iη Dᴴ` preserves the original order and sign; it is not
silently replaced with `(regularizedA)ᴴ`. Matrix inverses use determinant
nonvanishing where needed. `StrictStable` and `WeakStable` quantify over actual
characteristic roots; C02 proves their equivalence with concrete spectral
radius bounds. Disk and circle counts filter polynomial root multisets, so
algebraic multiplicities are retained. Rank is complex matrix rank, and
`hermitianImaginaryPart X` is exactly $(2i)^{-1}(X-X^*)$.

## The proof in four stages

| Contracts | Argument | Why its scope matters |
| --- | --- | --- |
| C01–C06 | Exact positive half, spectral semantics, pencil evaluation/degree, positive averaging and homotopy boundary nonvanishing. | Positivity is derived from the original circle condition; there is no limiting-imaginary-part positivity assumption. |
| C07–C14 | Fixed-grade Cayley transform, root-count homotopy, regularized count, ordered solution factorization and stability limits. | Grade $2n$ and multiplicity-preserving count arguments handle singular leading coefficients and changing actual degree. |
| C15–C19 | Limiting equation, reciprocal identity, selected spectrum count, Stein identity and nonzero simple-root pairing. | The reciprocal factors give $m$ selected circle roots and $n-m$ disk roots; simple roots at $±1$ receive the same treatment. |
| C20–C25 | Generalized Stein pairing, stable-space dimension/kernel inclusion, lower rank bound and rank-nullity. | Entire generalized eigenspaces are used; Jordan blocks inside the disk need no semisimplicity assumption. |

The bounded-degree disk homotopy proof passes through the fixed-grade Cayley
transform and a monic half-plane count theorem. That theorem uses bounded root
enumerations, compactness and continuity of the finite count. These are proved
lemmas, not a literature axiom for Rouché's theorem or the argument principle.
The grade convention includes roots lost through a degree drop without assuming
invertibility of $C$ or $D$.

`pencil_factorization` in `PencilAlgebra.lean` treats arbitrary $A,B,Q,X$ with
only `X.det ≠ 0` and $X+BX^{-1}A=Q$. It preserves the ordered matrix factors.
`pencil_polynomial_factorization` in `SolutionPolynomial.lean` turns that identity
into a determinant-polynomial identity by evaluation. Both the regularized and
limiting wrappers reuse these helpers; a stability premise is not introduced
into the limiting factorization by reuse.

At the limit, reciprocal root counts and weak stability identify the selected
spectrum. Simplicity on the unit circle yields a nonzero pairing through an
algebraic eigenfunctional argument. This supplies the lower rank bound without
an assumption that the Hermitian imaginary part is positive semidefinite.
For the upper bound, a double generalized-eigenvector induction in the Stein
identity shows that the full stable generalized eigenspace lies in the kernel.
Its dimension is $n-m$, including all stable Jordan multiplicities. Rank-nullity
then meets the lower bound at exactly $m$. The uniqueness hypothesis is unused
in the stronger theorem and retained in the canonical wrapper.

## Numerical and execution boundary

C01 uses only the exact certificate $0<1/2<1$, with kernel-mode LeanCert.
Its positive-half projection is actually consumed by C05. The actual local341
proof-body graph records the route from C25 through C24, C15, C13, C11, C06,
C05 to C01 and the checked certificate declarations. See
[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) for the precise bounds and route.
There is no numerical approximation to the input matrices or their spectra.

Root local340 passed the exact source closure, including 28 fresh compilations
and 10 authenticated reused successes. Local341 matched the universes and
binder-name-normalized types of all 25 contracts. The independent source
reviewers authenticated this evidence through read-only checks. The final real
Linux Comparator/default-kernel/sandbox verification remains not-run.
