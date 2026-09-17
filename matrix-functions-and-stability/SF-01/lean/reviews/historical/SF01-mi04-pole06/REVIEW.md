# SF-01 finite pole prefix — independent mathematical source review

**Approve these four new source modules for coordinated compilation.**
Reviewer `/root/mi04_independent_referee` is a nonauthor of SF01 and this prefix.
I independently read all305 new lines, the exact fifteen previously approved
statements, their frozen definitions and four public contracts, and required
pinned APIs. My earlier complete25-source review and the separate one-body
RidgeAlgebra repair approval are bound below. This is source approval only,
not a claim of Lean execution or complete SF01 verification.

PoleEnergy expands the actual matrix quadratic form into the positive pole
sum and b-inverse times the rank-one square. It proves symmetry entrywise,
then positivity using either a nonzero ordinary coordinate or the zeroth
coordinate and positive sqrt(a). Thus it handles an empty original pole family
(a one-dimensional pole matrix), zero weights and repeated poles. No weight
is divided by, and no positive-definiteness assumption replaces its proof.
The Mathlib PosDef introduction consumes the genuine quadratic form.

PoleDiagonalization uses the actual positive-definite matrix's real unitary
eigenvector matrix and positive eigenvalues. It converts the two inverse
identities to transpose identities and the opaque matrix spectral theorem to
P=Q*diag(lam)*transpose(Q). There is no sorting, simple-spectrum assumption,
numerical eigensolver, or data dependence on the later matrix input. The
orthogonal transpose-dot lemma uses Q*transpose(Q)=1, so its orientation agrees
with the transformed vectors in the residue proof.

PoleResidues proves the first column and then P*v=u for the explicit vector
v=e0*b/sqrt(a). Only b and sqrt(a) are cancelled, with their nonzero proofs
from ValidData. It proves u dot v=b independently. For every supplied valid
orthogonal diagonalization, transforming the actual solve gives lam_i*y_i=c_i.
Positive lam_i legitimizes c_i^2/lam_i=c_i*y_i; orthogonality then gives the
normalization sum b. Repeated eigenvalues and zero spectral coordinates cause
no exception. The additional reciprocal-weight sum1/b is exact scalar algebra.

The weaker reciprocal_weights_nonnegative theorem intentionally has no
ValidData hypothesis. Its square numerator and b-squared times positive-lam
denominator are nonnegative, so totalized real division proves its claim even
when b=0. That case is not silently used by the stronger normalization theorem,
which retains ValidData. No additional assumption reaches a frozen theorem.

All four mathematical obligations match the frozen Challenge headers exactly.
All fifteen helper/public headers match the statements reviewed before code.
The independent audit checks the complete29-source map, unchanged25 ancestors
(including the separately sealed Matrix-entry repair), all126 prior headers,
141 current declarations, nine frozen files and all24 public contracts. Eighteen
contracts now have source implementations, while six remain: block invertibility,
the matrix reciprocal identity, the data step, first Newton step, iterate ridge
representation and final canonical preservation. PoleChecks explicitly checks
the fifteen additions and imports the existing partial graph; it is not a
complete Solution and does not claim that those checks have executed.

Fourteen primary Mathlib files were hash-checked against literal pinned Git
commit0df444a360eaa60ab8c11dca51a86af692955474. The inspected APIs cover the
matrix spectral theorem/PosDef eigenvalues, entrywise Hermitian introduction,
real star/transpose, unitary identities, finite square sums, sqrt positivity,
single/diagonal/product actions, and real scalar coercion. The proof stays
symbolic in dimensions and uses the opaque matrix-level theorem to avoid
repeating eigenbasis construction. No new interval computation or resource
override is introduced; the earlier LeanCert half certificate remains in the
unchanged imported prefix and must still be checked in the eventual final graph.

Scoped Tau Ceti faithfulness/generalization review found no assumed conclusion,
vacuous custom predicate, narrowed dimensions or omitted degenerate cases.
Colbrook's mathematical authorship, George Stepaniants's Caltech department
and university, AI assistance and Apache2 credit remain. Reused Sidney Holden
IV03 source bytes and attribution are unchanged. No new email is included.

I ran no Lean/Lake/cache process, edited no proof/worktree/Git, and changed no
publication/count. Root owns the sole compiler. Actual elaboration, complete
final independent reviews, frozen-contract Linux Comparator/controls and an
exact published-commit rerun remain later gates.
