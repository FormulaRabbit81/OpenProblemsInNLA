# Pinned primary APIs and genuine project reuse

- Mathlib/Data/Nat/Init.lean260: Nat.strong_induction_on is ordinary well-founded
  induction over every strictly smaller natural. The proof target carries all
  dimension-dependent hypotheses, so the smaller matrix is passed explicitly.
- Mathlib/Analysis/Normed/Operator/Basic.lean390: ContinuousLinearMap.toNormedSpace
  supplies the normed-space scalar law for the actual operator norm. Existing
  SchurBasicNorms.schur_dimension_one has already used this same exact instance.
- Mathlib/Analysis/Normed/Module/Basic.lean50 and
  Analysis/Normed/MulAction.lean98: NormedSpace.toNormSMulClass and norm_smul.
  These are used for H n and its ContinuousLinearMap space, never the ambient
  Matrix norm. euclideanLin_smul_apply is the already-proved wrapper bridge.
- Mathlib/Analysis/Normed/Field/Basic.lean77: norm_inv.
- Mathlib/Analysis/Complex/Norm.lean106: Complex.norm_of_nonneg maps the norm of
  a real scalar cast into C to that nonnegative real. Data/Complex/Basic.lean141
  supplies Complex.ofReal_ne_zero. Together these justify every normalization.
- Mathlib/Algebra/GroupWithZero/Defs.lean55: mul_left_cancel₀ cancels a proved
  nonzero factor in the real saturation equality. Scalar-action associativity
  and field inverse identities give T=(operatorNorm T:C)•U.

Project sources are bound exactly in file02. SchurBasicNorms gives the diagonal
bound and actual dimension1 norm; SchurEndpoint gives the full scalar pair;
SchurReduction supplies concrete B/Z and all norms; SchurActiveBlock supplies
the actual smaller Toeplitz witness; SchurPairStep supplies all11 lifted clauses.
NormAttainment proves norm-zero iff matrix-zero, MaximalSpace identifies its
original Gram kernel with saturation, and Toeplitz.toeplitz_smul preserves an
explicit complex polynomial witness under normalization. No foundation is
reintroduced as an assumption or duplicated by an oracle.
