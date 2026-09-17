# SF-01 final finite Newton plan — second independent statement review

**Approve the exact eight auxiliary definition/alias bodies and28 proposed
statements for implementation.** Reviewer `/root/mi04_independent_referee` is
a nonauthor of SF01. I read the full plan, all definitions/signatures, original
canonical question, frozen definitions/contracts, required prior ridge/pole
results and pinned block/reindex/inverse APIs. This is a mathematical statement
review before new proof code; it certifies neither elaboration nor compilation.

The original real H-matrix predicate still uses the actual complex spectrum
of the comparison matrix. The final theorem keeps every n>=1, every admissible
real matrix, every k>=0 and the original recurrence X_next=(X+X_inverse*A)/2.
It adds actual unitness as a proved conclusion. The stronger manuscript's
other initializations/scalings and Halley extension are not claimed here.

The concrete block ordering is (pole index, matrix index). The proposed
Equiv.prodComm maps Mathlib's opposite blockDiagonal ordering to exactly that
ordering. Multiplication/one transport and inverse blocks preserve it. The
scalar lift has shape (r*n)-by-n and the matrix lift is Q tensor I. Compression
is U_transpose*B_inverse*U with the same actual dimensions throughout. The
generic statements remain valid for empty index types; actual pole matrices
have size d.size+1. No false nonempty premise or altered dimension is needed.

The block-unit argument has no circular dependency. B0's blocks are A plus
the nonnegative offsets; admissibility proves their units, including offset0.
The previously constructed actual pole diagonalization supplies positive
shifts for Bp, and orthogonal conjugation proves its unitness without requiring
A to be normal, Hermitian or positive definite. The previous independent ridge
comparison theorem already proves ridgeEval is a unit. Thus from R=A*F and
unit A one obtains unit F and F_inverse=R_inverse*A, in the required order.

The rank-update identity respects noncommuting multiplication. Writing
K=U_transpose*B0_inverse*U and F=bI+K gives
Bp*(B0_inverse*U)=b_inverse*U*F. Left cancellation by Bp_inverse and right
cancellation by F_inverse yield Bp_inverse*U=b*B0_inverse*U*F_inverse.
Consequently L=U_transpose*Bp_inverse*U=b*K*F_inverse and
F_inverse=b_inverse*I-b_inverse^2*L. No permutation of unrelated matrices
or unjustified inverse is used. All necessary unit assertions precede these
cancellations; the plan does not merely rely on totalized inverse notation.

The diagonalized compression gives L=sum c_i^2*(A+lam_i*I)_inverse. Combining
the earlier exact sum c_i^2/lam_i=b with the shifted-resolvent identity yields
reciprocalEval=b_inverse*I-b_inverse^2*L=R_inverse*A. This holds for every
supplied valid diagonalization; it does not assume distinct poles/eigenvalues,
nonzero weights or division by spectral differences. Empty original pole
families and zero residues are included. The stronger inverse identity uses
b>0 as required, without changing the separate weak b=0 nonnegativity theorem.

nextRidgeData is a transparent finite scalar record: it halves a,b, appends
old poles and positive lam values, and halves the old and reciprocal weights.
Its validity follows from the actual half coefficient and nonnegative weights.
Finite-addition splitting gives the exact half-sum evaluation. Critically,
Q and lam are selected from d before n and A. The existential d' therefore
precedes the universal dimension/input quantifiers; no dimension-dependent
choice or matrix-specific data is smuggled into the representation. The first
iterate follows from A_inverse*A=I, induction supplies the uniform data for
every k>=1, and k=0 uses the original admissible matrix and its proved unitness.

The static review binds the unchanged29-source precursor, all nine frozen
files, all24 original contracts and the exact six remaining public headers.
It compares all28 signatures with the recorded declaration map and checks
that the eight new modules do not yet exist. Six primary Mathlib files are
authenticated against literal pinned commit0df444a360eaa60ab8c11dca51a86af692955474;
the installed Lean4.33.1 Fin.addCases source is separately hash-bound, without
a fresh Git or execution claim. The auxiliary definitions contain no theorem
fields, proof assumptions, placeholder predicates or replacement target.

The proposed algebra stays symbolic, reuses opaque block/inverse facts and
the existing consumed kernel LeanCert half certificate, and adds no numerical
intervals, dimension enumeration or resource/trust relaxation. Scoped Tau Ceti
faithfulness/generalization checks found no missing hypothesis or target
narrowing. Authorship, affiliation, reused IV03 credit and privacy are preserved.
No proof/source/worktree/Git was edited and no Lean/Lake/cache or Comparator
was executed by this reviewer. Implementation, two complete source reviews,
actual builds, canonical controls/Comparator and exact publication reruns
remain required; no accepted count changes.
