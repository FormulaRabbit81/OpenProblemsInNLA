# SP-15 exact contracts 16–21: plan before implementation

Author: /root/mi13_full_referee2. Formalization contribution: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology. Substantial OpenAI Codex assistance; Fortier Bourque and Ransford
retain credit for the original question and generic finiteness theorem. No
email. This is author planning, not independent review or a Lean success claim.

The complete retained canonical README, solution.md and generated solution.tex
have been read. The route below proves the same determinant and all-shift
spectral conclusions as Section 1. It changes the second Schur pivot to reduce
formal algebra. It does not change any frozen definition or theorem header.

## Numerical and algebraic obligations first

Fix x in the actual open 1/16 parameter box. Put P=pMatrix x, Q=qMatrix x,
R=pRoot x and S=qRoot x. Actual contract 6 supplies Rᴴ=R, Sᴴ=S,
R²=P, S²=Q and units R,S. Contract 5 supplies positive definiteness of P,Q.
For an arbitrary complex z and positive real t, put ρ=normSq z and s=t+ρ.
Every real scalar in a complex matrix below is its actual ℝ→ℂ image.

1. ρ≥0, s>0, s≠0 and t≠0. Neither z≠0 nor ρ>0 is required.
2. sI₃ and K=s²I₃+tP are positive definite. The exact frozen K is retained.
   The alternative second pivot D=sI₃+Q is also positive definite and a unit.
3. The actual 9×9 regularized Gram matrix, after the frozen reindexing, has
   precisely the three-by-three block array

       [ sI,       −conj(z)R,       0       ]
       [ −zR,      sI+P,           −conj(z)S]
       [ 0,        −zS,            sI+Q    ].

   Contract16 itself is for every real t; positivity is only used later.
4. Eliminating sI gives the 6×6 block array [[X,B],[C,D]], where
   X=sI+(t/s)P, B=−conj(z)S, C=−zS and D=sI+Q. Its determinant is multiplied
   by s³. Prove the scalar equality 1−ρ/s=t/s from s=t+ρ.
5. D C=C D, proved from Q=S² and associativity; no P,Q commutation is used.
   BC=ρQ. With D invertible, prove

       det([[X,B],[C,D]]) = det(XD−BC).

   This follows from the bottom-right Schur complement and det_mul, because
   (X−B D⁻¹ C)D=XD−BC. It needs only C commuting with D, not B with X.
6. Preserve multiplication order in the exact identity

       XD−BC = s²I+t(P+Q)+(t/s)PQ
             = (t/s)·[(s³/t)I+s(P+Q)+PQ].

   Consequently s³·(t/s)³=t³ yields the exact contract18. Only scalar field
   identities may use commutative normalization. Matrix products never do.
7. For fixed z and equal coefficient functions, the characteristic polynomials
   agree at each point −(k+1), k∈ℕ, considered in ℂ. These infinitely many
   distinct points are obtained by the universal positive-t identity, not by
   finite evaluations. Matrix.eval_charpoly and det_neg connect them to the
   regularized determinant; the common factor is (−1)^9.
8. For arbitrary n, equal Gram characteristic polynomials imply equal ordered
   Gram eigenvalues with multiplicities. For k<n, their equal squared singular
   values and nonnegativity imply equal singular values. For k≥n, both actual
   singular-value functions are zero. This includes n=0 and repeated or zero
   singular values; no invertibility or simple-spectrum assumption is added.

No new interval computations, determinant expansion, numerical eigenvalue
computation, or sampling is required. The already proved kernel-mode LeanCert
certificate is consumed through the box, positivity and root prerequisites.

## Contract16: derive the Gram matrix from the construction

Use the pinned nested Sum-index block operations. Rewrite the one matrix as a
nested block diagonal identity, expand the actual conjugate transpose and
product with Matrix.fromBlocks_conjTranspose/fromBlocks_multiply and the
fromRows/fromCols product APIs, and simplify zero blocks. The three nonzero
diagonal products use contract6, and conjugate scalar products use the exact
normSq identity. Reindex the established block identity with the frozen
blockEquiv, using reindex_apply/submatrix_mul_equiv, submatrix_one_equiv and
conjTranspose_reindex. All nine block positions are covered. Avoid enumerating
81 scalar matrix entries or unfolding CFC.sqrt.

## Contract17: positivity without spectral calculations

Complex.normSq_nonneg and t>0 give s>0. Matrix.PosDef.one.smul gives sI and s²I;
the positivity of (t:ℂ)P and the add theorem give K. Use the pinned
ComplexOrder/MatrixOrder scopes and actual scalar coercions. Prove D positive
by adding Q to sI in the determinant module, when D is needed. No guessed
eigenvalue bounds or inverse norm bound enters this proof.

## Contract18: two small Schur complements

Split reusable block algebra from the public application if needed. Establish
the inverse of sI as s⁻¹I from its explicit multiplication identity and
invOf_eq_right_inv. Supply required Invertible instances from proved IsUnit
facts using nonempty_invertible; no inverse is assumed in a theorem hypothesis.

Apply det_fromBlocks₁₁ to the first 3+6 split, and prove its actual Schur
complement equals [[X,B],[C,D]] by block multiplication. Apply the helper from
obligation5 using det_fromBlocks₂₂. The short commutation proof only moves S
through sI+S²; it never moves P through Q. Apply det_smul in dimension3 and the
scalar cancellations to finish. Remove the 9×9 reindexing with det_reindex_self.

This is the same mathematical determinant formula as the canonical Section1,
but it avoids explicitly manipulating the inverse of K and the additional
det(sI+BC)=det(sI+CB) transport. Contract17 still proves K positive exactly as
frozen. All scalar divisions are justified by positive t and s; z=0 is covered.

## Contract19: polynomial identity on an infinite exact set

First derive equality of coefficientDeterminant x u s and the y version for
every u,s∈ℂ by the actual coefficient_determinant_identity contract7 and hxy.
For each k∈ℕ use t=(k+1:ℝ)>0 in contract18 on both x,y. At w=−(k+1:ℂ),
Matrix.eval_charpoly rewrites each evaluation as the determinant of the
negative regularized Gram matrix. det_neg supplies an identical factor.

The map k↦−(k+1:ℂ) is injective by negation, addition and natural-cast
cancellation. Set.infinite_range_of_injective and inclusion of its range in
the evaluation-equality set establish the exact hypothesis of
Polynomial.eq_of_infinite_eval_eq. This avoids changing coefficient fields,
root multiplicity reconstruction or a degree-specific Vandermonde calculation.

## Contracts20–21: actual ordered singular values

Read and reuse the short method of the accepted MI13 gram_charpoly and
singular_values_gram proofs, with retained code attribution and source hashes.
Its public module imports unrelated operator-norm/Frobenius proofs, so the
standalone SP15 candidate should use the same pinned primary APIs directly in
a light GramSemantics module rather than import the whole MI13 proof graph.
There is no existing single Mathlib theorem for this exact combined statement
in the inspected source search; the mathematical steps are already library
theorems, not newly assumed spectral results.

Matrix.toEuclideanLin_conjTranspose_eq_adjoint and toLpLin_mul identify the
actual adjoint-composition linear map with the matrix Gram operator. Change to
the orthonormal-basis toLin representation, then use Matrix.charpoly_toLin.
The symmetric-operator eigenvalues_eq_eigenvalues_iff transports the actual
Gram characteristic-polynomial equality. Use sq_singularValues_fin,
singularValues_nonneg and sq_eq_sq₀ for k<n, and
singularValues_of_finrank_le for k≥n, with the exact Euclidean finrank theorem.

Contract21 applies contract20 to the two actual shifted matrices at every
z:ℂ and every k:Fin9, with contract19 as its Gram equality. No restriction on
the phase, magnitude, real/complex status or vanishing of z is introduced.

## Implementation gates and bounded module order

Suggested modules: BlockGram for16; SchurPositivity for17; SchurAlgebra and
ShiftedDeterminant for18; GramPolynomial for19; GramSemantics for20; then
ShiftedSpectrum for21. Source-first acceptance is required before implementation.
Each exact theorem retains its frozen header and genuine prerequisites. Root
alone runs the serial compiler with unchanged resource limits, records failed
attempts and reuses only matching successful outputs. No proof or local/runtime
success is claimed by this plan. No problem count changes.
