# MI-13 independent statement review

**Approve the exact proposed semantic boundary for local statement elaboration.**
Reviewer `/root` did not author these Lean definitions or contracts. This is a
statement and mathematical-route review, not a completed proof review, compiler
run or authorization to count this problem as verified. The second independent
review and actual statement elaboration remain required before freezing.

I read the entire original 126-line canonical page, the numerical targets,
pre-code 36-contract plan, all Definitions and all 36 complete Challenge
headers, correspondence, and complete informal finite route/obligations. I
read the pinned Tau Ceti correctness, generality, proof-quality, reuse and
attribution rubrics and applied them at the independent-contract project scope.
I inspected the exact pinned singular-value definitions and square identities,
sorted eigenvalues/eigenbasis, and partial-index orthonormal extension APIs.

The final contract is precisely the original rectangular complex inequality,
with m,n at least two, A,C of shape m by n and B of the opposite shape. The
coefficient is two. No rank, reality, nonzero, invertibility, spectral-gap or
supplied-SVD assumption is present in the target. The two zero-indexed singular
values correspond to the original first two values. They are actual Mathlib
singularValues of the Euclidean linear map; the operator norm is the genuine
CLM norm, and the Frobenius norm is the Euclidean norm of all flattened entries.
The separate trace/Gram identities must be proved and prevent accidental use
of an entrywise sup norm or an unordered eigenvalue pair.

Every helper is mathematically valid including its degenerate cases. The
positive-index image extension has a direct pinned library implementation
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`; use it rather than
reproving rank-count machinery. `sq_singularValues_fin`, antitonicity and zero
extension likewise supply genuine existing foundations. GramBasis is a
predicate on a supplied basis, with unrestricted existence separately required;
it is not an oracle or extra final assumption. Zero singular images follow
from the actual Gram energy identity and are handled before extending the
positive images. Empty generic dimensions do not introduce a contradictory
global Nonempty instance.

I checked the internal refined commutator route algebraically. On the actual
Hilbert space of entries, D=ad(X) has adjoint ad(X*); T=D*D is positive.
J(Y)=[X*,Y*] is conjugate-linear with J²=-T, TJ=JT, and trace cyclicity gives
orthogonality of Y and JY. A positive eigenvalue therefore supplies two
independent eigenvectors. The functional kernel combination is nonzero;
its vanished transformed (0,0) commutator entry eliminates precisely the sole
coefficient that could exceed s0²+s1². All other coefficients obey the
two-coordinate complex Cauchy–Schwarz estimate. The two unitary Frobenius sums
give the factor two, and a nonzero top eigenvector permits cancellation. The
zero maximal-eigenvalue branch needs no division. The refined commutator result
is an actual required theorem, never an assumed external inequality.

The contraction average uses every singular value in [0,1] and the exact
unit-circle square-root identities, including endpoints. It covers singular
and zero matrices. The unrestricted middle factor is rescaled only after
separating zero. Upper/lower sum-block padding gives the original rectangular
three-factor product; actual norm and all zero-extended singular-value
preservation are exposed as separate full obligations, including rank zero
and one. Padding to m+n replaces max(m,n) without changing the dimension-free
constant. The diagonal(1,-1), identity, matrix-unit endpoint gives four on
both sides and correctly checks normalization.

The only proposed LeanCert calculation is positivity of one-half in kernel
mode, genuinely consumed by the squared-norm averaging bound. The unit-circle
and all matrix estimates remain symbolic. No interval enumeration is needed.
The independent Challenge wrappers expose the semantic boundary and have real
downstream consumers; they are not proposed as a duplicated general Mathlib API.
Nobori, Audenaert and the repository reduction keep mathematical attribution;
George Stepaniants receives formalization credit with Caltech Computing and
Mathematical Sciences and no email. No new mathematical priority is claimed.

The accompanying Python audit authenticates all sealed draft bytes and the
numerical-first record, compares all 36 headers and Comparator names, verifies
the original literal Git source and three exact pinned primary library files,
and checks the absence of proof implementation. This is static review only:
the 36 Challenge holes are deliberate specifications, and no successful Lean,
LeanCert, Comparator, completed-project validator, Linux control or publication
execution is implied. Any elaboration repair must be reviewed at its actual
scope before the final immutable boundary is frozen.
