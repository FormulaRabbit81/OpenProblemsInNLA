# Schur scalar endpoint and active block: pre-code plan

PLAN ONLY. Proposed exact frozen contracts 9 (schur_scalar_endpoint) and 13
(schur_active_block), in new SchurEndpoint.lean and SchurActiveBlock.lean.
Await root's approval before writing any proof source. Current sealed contracts
47/49 and their candidates remain unchanged; prioritize actual local feedback
on them before implementation. No compiler, Lake, cache mutation, Git or
network command is part of this task.

## Exact numerical and semantic obligations

Contract 9 has n>=1, U=toeplitz n p, actual Euclidean operator norm ||U||=1,
and |p_0|=1. Prove U=p_0 I and the entire frozen SchurPair n U 0 (C p_0) 1,
including all polynomial, disk/boundary, coprimality, matrix action, maximal
subspace parameterization and finrank clauses. The symbol p has no degree
bound. Only its coefficients visible in the n-by-n Toeplitz matrix can be
forced to vanish; do not assert p=C p_0 as a polynomial.

Contract 13 has Z of size n+1, Toeplitz, zero diagonal, and actual operator norm
at most one. Here n may be zero. Prove that the precisely frozen submatrix
V_ij=Z_(i.succ,j.castSucc) is Toeplitz and has the same actual operator norm as
Z. For every complex Euclidean g and complex eta, prove all three clauses:
  Z appendVector(g,eta) = prependZero(Vg),
  ||appendVector(g,eta)||² = ||g||² + |eta|²,
  ||Z appendVector(g,eta)|| = ||appendVector(g,eta)||
    iff eta=0 and ||Vg||=||g||.
The input appends the scalar at the LAST coordinate; the output prepends zero
at the FIRST coordinate. These are different coordinate embeddings and must
not be interchanged. At n=0, V is the zero-dimensional map, Z is a 1-by-1 zero
matrix, g is its unique zero-dimensional vector, and the equivalence reduces
to |eta|=0 iff eta=0. No false norm-of-identity-one claim is used in dimension0.

Only real squared norms, finite nonnegative sums and symbolic coordinate
identities are needed. The complex field and actual Euclidean norms are
retained. No interval computation or new LeanCert certificate, SVD, spectral
oracle, rank assumption, or norm-attainment existence assumption is needed.
The final canonical n>=2, nonzero complex lam and 1<=k<n scope is untouched.

## Contract 9: scalar endpoint and full SchurPair

1. Let e_0 be the actual Euclidean single-coordinate unit vector. Use the
   coefficient matrix definition and its finite coordinate sum to prove
   (U e_0)_i=p_i for every i:Fin n. The operator-norm application bound and
   ||e_0||=1 imply ||U e_0||<=1.
2. EuclideanSpace.norm_sq_eq gives sum_{i:Fin n}|p_i|²<=1. The i=0 term is
   exactly one. Split it off with Finset.add_sum_erase. The remaining sum is
   both nonnegative and at most zero, so is zero. The nonnegative-sum equality
   theorem forces each remaining squared norm to be zero. Thus p_j=0 for
   every 0<j<n. This argument does not require a degree bound on p and uses
   the primary Euclidean norm identity directly.
3. Compare matrix entries, using the zero coefficients for strictly lower
   entries and the Toeplitz zeros above the diagonal. Obtain U=p_0 I.
4. Scalar matrix action is p_0 • x, by the primary Matrix.toLpLin identities.
   Its norm equals ||x|| since |p_0|=1. The already-proved exact
   maximal_space_norm characterization and ||U||=1 show every vector is in
   maximalSpace U. Establish this submodule is top, without choosing a basis
   of singular vectors or imposing a simple singular value.
5. Supply every SchurPair conjunct explicitly:
   - d=0<n; p_0!=0 follows from |p_0|=1, so degree(C p_0)=0;
   - degree(1)<=0, coefficient(1,0)=1, and C p_0 is coprime to 1;
   - the denominator evaluates to one everywhere, and both the disk bound
     and unit-circle equality reduce to |p_0|=1;
   - U*toeplitz n 1=toeplitz n(C p_0) by the proved Toeplitz one/constant laws;
   - for every x choose h=vectorPolynomial x. coefficient_roundtrip gives
     x=coeffVector n h and DegreeLT h n. Convert the zero-polynomial branch
     or natural-degree <n branch to DegreeLE h (n-1), using n>=1. The reverse
     subspace implication follows from maximalSpace U=top;
   - for every allowed h, Toeplitz action plus coeffVector_mul_truncate gives
     U coeffVector n (1*h)=coeffVector n ((C p_0)*h). This action actually
     needs no extra degree hypothesis; the exact frozen one is retained;
   - use Module.finrank_top and finrank_euclideanSpace_fin to identify the
     maximal-space finrank with n=n-0.

This proves the whole endpoint SchurPair, not just that the matrix is scalar.

## Contract 13: exact coordinate compression

1. Choose a Toeplitz symbol p for Z. Its zero diagonal at the valid index
   0:Fin(n+1) gives p_0=0. For V use the existing polynomial divX p as the
   witness: its coefficient at j is p_(j+1). Entrywise, split j<=i versus
   j>i. The boundary case j=i+1 contributes p_0=0; all other out-of-range
   entries are already Toeplitz zeros. Obtain V=toeplitz n (divX p).
2. Prove the first row and last column of Z are zero from the same Toeplitz
   formula and p_0=0. No new triangular-matrix assumption is added.
3. Prove the action by splitting output index zero/successor and the input
   finite sum into castSucc entries plus the last entry. The latter vanishes
   by the zero last column, while each remaining entry is definitionally the
   active block. Fin.snoc_castSucc/snoc_last and Fin.cons_zero/cons_succ keep
   the two coordinate placements explicit.
4. Prove the append squared-norm identity from EuclideanSpace.norm_sq_eq and
   Fin.sum_univ_castSucc. Prove prependZero preserves norm from the same
   identity and Fin.sum_univ_succ. Derive ||g||<=||append(g,eta)|| and
   ||append(g,0)||=||g|| using nonnegative-square comparison. These facts hold
   for n=0; no unit vector in H0 is chosen.
5. Every x:H(n+1) has the exact decomposition append(g,eta), with
   g_i=x_(i.castSucc) and eta=x_(last n), from Fin.snoc_init_self. Prove the
   two operator-norm inequalities using ContinuousLinearMap.opNorm_le_bound:
   - test Z on append(g,0) to bound ||Vg|| by ||Z|| ||g||, giving ||V||<=||Z||;
   - decompose arbitrary x as append(g,eta), use ||Zx||=||Vg|| and
     ||g||<=||x||, giving ||Z||<=||V||.
   This avoids dimension-sensitive norm attainment and works unchanged at n=0.
6. Transfer hcon to ||V||<=1 and hence ||Vg||<=||g||. If equality of the
   full norms holds, square the action identity and append norm formula:
   ||Vg||²=||g||²+|eta|². Contractivity makes |eta|²<=0, so eta=0; the remaining
   equality is ||Vg||=||g||. Conversely these two conditions immediately give
   the original full norm equality. Use hcon exactly in this forward defect
   argument; the algebraic action and norm comparison need no stronger bound.

## Pinned primary reuse and practical source interfaces

All Mathlib reads use pin 0df444a360eaa60ab8c11dca51a86af692955474. Bind complete
source-file hashes in the pre-code record. Important inspected interfaces:
- Analysis/InnerProductSpace/PiL2.lean:151 EuclideanSpace.norm_sq_eq;
  :202-208 finite Euclidean finrank. PiLp.single norm/application and PiLp.ext
  provide standard-vector and coordinate identities.
- Analysis/Normed/Operator/Basic.lean:199 opNorm_le_bound and :237 le_opNorm.
- Algebra/Order/BigOperators/Group/Finset.lean:192 generated
  sum_eq_zero_iff_of_nonneg; BigOperators/Group/Finset/Basic.lean:740 generated
  add_sum_erase. Nonnegative squared norms are the hypotheses, not assumed
  positive coefficients or a nonempty remainder sum.
- Algebra/Polynomial/Inductions.lean:40-45 divX and coeff_divX. This is the
  polynomial's explicit coefficient shift, not a field-division oracle.
- Data/Fin/Tuple/Basic.lean:117-120 cons coordinates; :526,539 snoc coordinates;
  :602 snoc_init_self for the exact decomposition of every vector.
- Algebra/BigOperators/Fin.lean:76,85 generated sum_univ_succ and
  sum_univ_castSucc for leading and trailing coordinate sums.
- LinearAlgebra/Dimension/Finrank.lean:139 finrank_top;
  Polynomial/Degree/Defs.lean:149 degree_C and natural-degree/degree bridges;
  RingTheory/Coprime/Basic.lean:97 isCoprime_one_right.
- Existing coefficient_roundtrip, toeplitz_action, coeffVector_mul_truncate,
  toeplitz_one, toeplitz_C, and maximal_space_norm are used directly. The
  scalar action uses the same primary Matrix.toLpLin map_smul/toLpLin_one
  interface already locally checked in SchurBasicNorms.

Implementation risk is confined to the familiar PiLp/matrix coordinate
wrappers, finite-index arithmetic, and submodule coercions. Each needed
representation-only `change` will be commented. The complete mathematical
route above has no known obstacle, but source elaboration and independent
proof review have not been run. A failing wrapper must be repaired locally
without changing the statement. The author will not run the compiler.

Preserve all frozen definitions, exact headers, pins, kernel trust assertions,
original credits, and George Stepaniants' Caltech Computing and Mathematical
Sciences affiliation without email. These are two Schur foundation contracts,
not the complete finite Schur induction or canonical IE-02 minimax target.
