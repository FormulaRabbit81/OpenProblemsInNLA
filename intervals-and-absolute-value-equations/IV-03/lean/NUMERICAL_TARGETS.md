# IV-03 statement plan — complete original target

Work in progress, before proof implementation. Mathematical source: Matthew J. Colbrook's complete IV-03 manuscript, Theorem 1, read in full at the exact commit recorded in SOURCE_PROVENANCE.json. Formalization draft by Sidney Holden with AI assistance. No verification is claimed.

Retain every dimension n≥1 and every pair of real matrices L≤U entrywise. Every entry varies independently, with closed endpoints; widths may be zero. No regularity, symmetry, irreducibility, strict positivity of entries, or nonsingularity premise on the interval is added.

An inverse-M matrix is genuinely invertible, is entrywise nonnegative, and its actual inverse has nonpositive off-diagonal entries. This is precisely the inverse of an invertible Z-matrix with nonnegative inverse. The invertibility guard prevents the totalized matrix inverse at a singular matrix from satisfying this property accidentally.

The center and radius are exactly (L+U)/2 and (U−L)/2. The i-th sign vector is −1 at i and +1 elsewhere. The vertex expression is C+s D_i R D_j, for s in {−1,+1}; an explicit formula theorem connects its pointwise definition with actual matrix multiplication. Both signs and all n² ordered pairs occur in the original criterion. Repetitions are harmless, including n=1 and zero widths.

The source's stronger n² negative-sign criterion implies the full two-sign criterion without weakening it. Both are required as conclusions. All members, including potentially singular members, occur in the quantified interval. The intended induction uses proper principal submatrices and Schur complements; an adjugate completion argument proves determinant positivity instead of assuming it. Dimensions one and two need their actual separate arguments. In dimensions at least three, the source controls the signs of Schur-complement derivatives throughout the full box. Every closure, differentiability, cofactor and monotonicity bridge must be proved or imported from checked Mathlib; no key source lemma is to become an assumption.

This is a symbolic all-dimensional theorem, so no finite sample or artificial interval grid is a substitute. Minimize computation by exact endpoint arithmetic, sign symmetry and the stronger negative-sign family, retaining all original matrices. Polynomial complexity and the stronger operation count discussed after the theorem are not part of the canonical equivalence and are not claimed.

The four Challenge declarations are deliberate placeholders establishing no mathematics. Two independent nonauthor reviewers must approve the numerical plan, actual definitions and typechecked signatures before proofs. A future Solution must not import Challenge. Every export must undergo LeanCert kernel trust auditing, all-axiom audit, actual isolated Linux Comparator and negative controls before any success claim. No original problem ID, path or status changes at this stage.
