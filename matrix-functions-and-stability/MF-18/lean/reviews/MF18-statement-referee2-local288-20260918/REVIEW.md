# Independent MF-18 statement review, exact local288 boundary

I approve the 25 exact elaborated statement contracts and transparent definitions
identified in `SCOPE.json`. They cover the unchanged original complex Green-rank
target. I found no mathematical statement blocker. This approves a statement
boundary before proof implementation; it does not approve a Lean proof, a solved
claim, publication, or any increase in the verification count.

I am `/root/nm04_final_referee1`. I did not author the MF-18 mathematical solution,
candidate definitions, or Lean proof code, and I did not read the other new
statement review before recording this verdict. I independently derived the
target from the canonical README and full source solution, then inspected every
definition and contract. `IndependentChallenge.lean` retains the exact candidate
types after that derivation; its new introductory comment identifies this
provenance. Its deliberate placeholders are not proofs. I did not run Lean,
Lake, Comparator, or a GitHub workflow, and did not change candidate sources.

The retained draft manifest is
`504737b3bc65db25dcf445e857750e55177dc23bcbccd5a0e50dc77d7d018a20`.
The exact elaborated packet manifest is
`dbfb4b941b16c103a762f5bd81c3b5c3f10f9796c1685787197429f8a386325c`.
The reviewed Definitions, Challenge, and Comparator configuration are copied
under `reviewed/`; their hashes and the primary source hashes are in `SCOPE.json`.
The upstream target/source snapshot is commit
`e7519c46fd249a6a033bfe5d11c66bf47f7f8885`. The pinned Tau Ceti correctness,
generality, proof-quality, attribution, and reuse rubrics inform this review;
their exact bytes are retained in the hash-bound draft. I did not treat an
earlier informal independent review as a substitute for my own assessment.

## Independent derivation of the target

The original quantifiers are arbitrary positive finite dimension and complex
matrices C,D,R,P, with R and P Hermitian and strict circle positivity. The given
family is nonsingular, satisfies the regularized Riccati equation and strict
spectral-radius stability at every positive eta, and has a finite nonsingular
right limit X0. The determinant pencil is regular; its unit-circle roots are
algebraically simple and number 2m. The conclusion is the complex rank m of
H=(X0-X0*)/(2i). Nothing in the candidate restricts entries to real numbers,
requires C or D invertible, assumes commuting matrices, diagonalizes the stable
part, imposes a spectral gap, or assumes H positive semidefinite.

`Mat n` and `Vec n` are literal complex matrices and vectors on `Fin n`.
`[NeZero n]` on the final statements means the original n>=1. `GreenAssumptions`
contains the stated input hypotheses only. In particular it does not contain the
rank identity, a root count for the selected solution, a Stein-kernel condition,
or a selection oracle. The final wrapper adds the original uniqueness condition;
the preceding theorem is valid under the stronger claim that uniqueness is
unnecessary. Quantifying a total real-indexed family causes no restriction:
only positive eta and the right-limit filter are used.

The pencil is det(lambda^2 C* - lambda R + C), with multiplicities represented
by the multiset `Polynomial.roots`. `SimpleCircleRoots` uses actual
`rootMultiplicity = 1`, not geometric multiplicity. Explicit regularity
prevents the zero polynomial's empty root multiset from hiding a failure.
`hermitianImaginaryPart` is the Hermitian imaginary part, not entrywise imaginary
components. The `Matrix.rank` conclusion is over the complex scalar field.

I checked the delicate regularization sign separately: B_eta=C*+i eta D*,
which is generally not A_eta*. Both the equation and the factorization use the
correct B_eta. The `ComplexOrder` instance makes positivity of the Hermitian
quadratic form mean a positive real value with zero imaginary part; this is the
usual complex positive-definite matrix predicate, not a lexicographic order.

## Every selected contract

The C numbers below record the order in `comparator.json`.

| Contract | Independent mathematical check and role |
| --- | --- |
| C01 `certified_half` | The exact rational inequalities 0<1/2<1 are true. The positive half is intended for averaging positivity at +1 and -1, supplying P>0 for the homotopy. This review does not claim the future LeanCert certificate has run or is consumed. |
| C02 `stability_semantics` | For a nonempty finite complex matrix the roots of its characteristic polynomial are its spectrum; maximum modulus <1 is precisely spectral radius <1. The result connects the transparent root predicate to the original stability assumption. |
| C03 `pencil_evaluation` | Evaluation is a ring homomorphism through the determinant; the entry polynomial has the correct coefficient order and signs. |
| C04 `pencil_degree_bound` | Every entry has degree at most two, so every determinant summand has degree at most 2n. This is a grade bound, not an unjustified equality when C is singular. |
| C05 `positive_average_and_sign` | Circle positivity at +/-1 gives P by positive averaging. Substitution of -lambda gives the minus-sign weight W(lambda). |
| C06 `homotopy_boundary_nonvanishing` | Multiplication by lambda^-1 on the circle gives a Hermitian part minus i eta times ((1-t)P+tW). The latter is positive definite for all t in [0,1], so a kernel vector would contradict its nonzero imaginary quadratic form. |
| C07 `cayley_degree_and_count` | Homogenizing to grade N and dividing by p(1) makes a monic polynomial of exact degree N. The map lambda=(z-1)/(z+1) sends the right half-plane to the disk. Multiplicities are preserved; degree-drop roots at z=-1 are on the left and do not enter the count. Constants and N=0 are included. |
| C08 `cayley_boundary_transfer` | Finite points with Re z=0 map to the unit circle and z+1 is nonzero there. Thus the transformed polynomial has no boundary zero. The normalizer p(1) is nonzero by the full boundary hypothesis. |
| C09 `monic_half_plane_count_homotopy` | Continuous coefficients, fixed monic degree, and absence of imaginary-axis roots make the multiplicity count locally constant. Root collisions do not invalidate multiplicity counting; the fixed degree excludes escape to infinity. This is a substantial proof obligation, not a supplied oracle. |
| C10 `bounded_degree_disk_count_homotopy` | C07-C09 transfer the bounded-grade disk problem to fixed-degree monic polynomials. Actual degree changes are allowed. |
| C11 `regularized_root_count` | At t=0 the determinant is a nonzero constant times lambda^n because P>0. C06 and C10 preserve its n disk roots through t=1. Singular C or D is harmless. |
| C12 `solution_factorization` | Expanding (lambda B X^-1-I) X (lambda I-X^-1 A) gives lambda^2 B-lambda(X+B X^-1 A)+A, hence the required pencil. Only X invertibility, already explicit, is used. |
| C13 `complementary_stability` | Strictly stable S supplies all n disk roots. The complementary factor has none in the closed disk. A nonzero eigenvalue mu of B X^-1 with norm >=1 would yield a forbidden complementary root lambda=1/mu; zero eigenvalues are already strictly stable. No inverse of B is assumed. |
| C14 `closed_disk_stability_limit` | Characteristic polynomials have fixed monic degree n and coefficient convergence. Roots of the limit cannot lie outside the closed disk. The claim also holds for n=0. |
| C15 `limiting_equation_and_spectra` | Continuity of matrix inverse at nonsingular X0 gives the limiting equation. Applying C14 along any positive sequence tending to zero gives both weak spectral bounds. No differentiability or continuity away from the limit is needed. |
| C16 `reciprocal_count_identity` | Hermitian R gives the grade-2n conjugate reciprocal symmetry. If actual degree is d and zero multiplicity z, then d+z=2n. Nonzero roots off the circle pair under lambda -> 1/conj(lambda), giving 2*disk+circle=2n even when leading or constant coefficients vanish. |
| C17 `selected_spectrum_count` | Limit factorization and complementary weak stability exclude complementary roots inside the disk. All n-m interior roots of the regular pencil therefore belong to the monic degree-n characteristic factor, leaving m boundary roots. Simplicity is inherited from the original determinant factorization. |
| C18 `stein_identity` | Subtract the adjoint limiting equation and multiply out the inverse-difference identity. This gives H=S*HS and the literal H is Hermitian. |
| C19 `simple_unit_root_pairing` | See the adjugate/derivative check below. Algebraic simplicity, not a new crossing assumption, forces v*Hv nonzero for each nonzero selected unit eigenvector. |
| C20 `generalized_stein_pairing` | Expand the Stein identity on generalized eigenvectors and induct on the two nilpotent orders. The coefficient 1-conj(lambda)mu is explicitly nonzero. Order-zero cases force a zero vector and need no exception. |
| C21 `stable_space_dimension` | Generalized eigenspaces over C are independent and span by the primary decomposition. Their dimensions are the characteristic root multiplicities. The supremum over norm<1 eigenvalues therefore has dimension equal to the disk multiset count, including all Jordan chains. |
| C22 `stable_space_in_kernel` | Put a stable generalized vector in the second slot of C20 and an arbitrary generalized eigenvector in the first. Weak stability makes every pairing nonresonant. The first-slot spaces span, so Hw=0. H need not be Hermitian for this stronger helper. |
| C23 `stein_rank_lower_bound` | Distinct unit eigenvalues are nonresonant. Their eigenvectors give a diagonal Gram matrix with nonzero diagonal. Its rank is the number of simple unit roots and is bounded by rank H. No condition on nonunit Jordan blocks is needed. |
| C24 `full_complex_rank` | C17 and C21 give stable dimension n-m; C22 gives rank H<=m. C19 and C23 give rank H>=m. All original hypotheses are present; no result is hidden in an extra premise. |
| C25 `canonical_full_complex_rank` | Adds the original uniqueness condition without changing the conclusion. This is the literal original-target wrapper, while C24 records the valid stronger theorem. |

## Adversarial boundary and derivative checks

I separately tested the proposed argument at singular coefficients, degree drops,
m=0, n=1, lambda=+1 and -1, and defective stable blocks. At C=0 and invertible R,
the unregularized pencil is a nonzero constant times lambda^n: d=z=n, disk=n,
circle=0, consistent with C16. Grade 2n rather than actual degree is essential.
The Cayley normalization excludes lambda=1 only at the regularized homotopy,
where full boundary nonvanishing proves the exclusion. It imposes no exclusion
on +/-1 roots of the limiting polynomial. With m=0, the stable space is the whole
space and C22 gives H=0, as required. Helpers allowing n=0 are also consistent
with determinant 1, characteristic polynomial 1, and zero-dimensional spaces.

For C19 let F=lambda^-1 P0(lambda). On the unit circle F is Hermitian. The
selected eigenvector satisfies Cv=lambda X0v and therefore Fv=0. Simplicity of
the determinant root makes P0'(lambda) nonzero at determinant level and forces
nullity exactly one: nullity at least two would make the adjugate zero and hence
the determinant derivative zero. Thus adj(F)=kappa vv* for a nonzero real
factor after absorbing the normalization of v. Since
adj(P0(lambda))=lambda^(n-1)adj(F), the determinant derivative forces
v*P0'(lambda)v != 0. Using the null equation and Cv=lambda X0v gives

    v*P0'(lambda)v = v*(X0*-X0)v = -2i v*H v.

This identity is valid for arbitrary nonzero v, n=1, and both unit endpoints.
The draft does not assume that identity's nonvanishing as an input hypothesis.
Likewise C22 really gives the right kernel: the stable vector is the second
pairing argument. This avoids an accidental left-kernel assertion in the
non-Hermitian general helper.

## Exact elaboration delta and actual evidence

The original draft remains untouched. I read the complete delta to the candidate:
the reserved binder lambda was uniformly renamed `lam`; `ComplexOrder` was
opened; the complementary determinant and maximal generalized eigenspace calls
were explicitly qualified. The exact determinant entries, parameter order,
quantifiers and mathematical expressions are preserved. I checked the selected
complex-order instance, `Matrix.PosDef`, `maxGenEigenspace`, and the zero
polynomial root-multiplicity convention in pinned Mathlib sources.

I inspected the actual root-run local288 receipt and both full MF-18 logs.
Definitions and Challenge were freshly elaborated, with source hashes matching
the reviewed bytes, exit code zero, one thread and a 4096 MiB cap. Definitions
took about 7.12 seconds; Challenge about 4.01 seconds. The Challenge log contains
exactly the 25 intentional placeholder warnings. Its dependency output hash is
the recorded fresh Definitions output hash. The other nine modules in the
mixed run are outside this MF-18 statement-review scope. I do not describe
this as a full MF-18 proof build or as an independent compiler rerun. The
earlier syntax failure is honestly distinguished from this successful run.

The historical proposal comments still say the draft had not been elaborated;
the separate `ELABORATION.json` records the later actual elaboration correctly.
They should be refreshed in future publication documentation, not interpreted
as a second execution record or a reason to alter the mathematical boundary.

After reading its complete implementation, I executed the draft's read-only
integrity checker: actual tool chunk `5ee6c9`, PASS, 64 payloads, 23 bound
sources, 22 library bindings and 25 contracts. My own `verify_review.py` performs
byte, delta, coverage and retained-evidence checks only. It invokes no external
process, compiler, or network and cannot certify mathematical truth. Its actual
result is retained separately. The final Linux Comparator run, kernel/sandbox
controls, proof reviews, and proof-body LeanCert consumption check remain future
gates. No complete-verification or new-resolution count changes here.

## Remaining implementation and publication requirements

The fixed-degree root-continuity/count argument, determinant derivative bridge,
reciprocal multiplicity count and generalized Stein pairing require real Lean
proofs. Library reuse should preserve provenance and make significant
representation changes explicit. They must not become assumptions to shortcut
the final theorem. Computational work should remain symbolic at arbitrary
dimension; circle sampling or finite matrix experiments cannot discharge these
contracts. One exact rational LeanCert certificate is enough for the stated
scalar obligation, but its use in the final dependency graph must be checked.

Future publication must include truthful `formalization.yaml`, exact Comparator
contracts, two nonauthor final code reviews, and actual final Linux evidence.
Preserve George Stepaniants's name, Department of Computing and Mathematical
Sciences, California Institute of Technology, and prior Guo--Kuo--Lin/Colbrook
attribution. Do not publish his email. This compact review does not repackage
the whole historical evidence archive or certify current upstream merge status.
