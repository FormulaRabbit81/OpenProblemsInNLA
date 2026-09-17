# SP-15 exact obligations before Lean proof implementation

Prepared for George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Substantial AI assistance. Fortier Bourque and Ransford retain credit for the original question and generic finiteness result. This is a proposed statement-first formalization plan, not independently accepted Lean statements or a completed proof.

## Full original negative target

For every integer M≥1, produce a family A:Fin(M+1)→Matrix(Fin 9)(Fin 9) ℂ such that:

- for all i,j, every z:ℂ, and every k<9, the actual kth decreasing singular values of Aᵢ−zI and Aⱼ−zI are equal;
- for every i<j and every complex 9×9 U with U*U=I, Aⱼ≠U*AᵢU.

This refutes the original universal finiteness statement at N=9. The conclusion must have no assumed local fiber, coefficient identity, unitary-inequivalence theorem or external constant-rank theorem. A finite collection of sampled shifts or just the largest singular value would be insufficient.

## Concrete parameter definitions

Write x=(p₁,p₂,p₃,q₁,q₂,q₃,a,b,c,d)∈ℝ¹⁰, with coordinate order fixed exactly as written. Define

    P(x)=diag(p₁,p₂,p₃),
    Q(x)=[[q₁,a,b],[a,q₂,c+id],[b,c-id,q₃]],
    x*=(1,2,3,4,4,4,1,1,1,1), δ=1/16,
    B={x: |xⱼ−x*ⱼ|<δ for every coordinate j}.

The open box B is the only parameter domain needed. It is an allowed restriction of the constructed counterexample family, not a weakening of the original universally quantified question.

For x∈B, prove P,Q positive definite, 0<p₁<p₂<p₃ and a,b>0. The exact kernel-mode LeanCert scalar contract proposed for genuine consumption in this step is

    0<δ, 0<1−δ, 0<1−2δ, 3(1+δ)<4−δ, 4−δ−3(1+δ)=3/4.

Use |c+id|≤|c|+|d|. Every Q diagonal is >63/16; each off-diagonal row norm sum is <51/16 (the first row has an even smaller sum). The existing Gershgorin theorem and Hermitian eigenvalue positivity characterize positive definiteness. No interval subdivision, eigenvalue approximation, or cube subdivision is required. The same disjoint intervals for p₁,p₂,p₃ will rule out unitary permutations directly.

Let X=CFC.sqrt(P), Y=CFC.sqrt(Q), the genuine positive definite Hermitian square roots, and

    A(x) = [[0,X,0],[0,0,Y],[0,0,0]].

Use an explicit finite-index reindexing to identify the three blocks with Fin 9. Prove the square-root identities and invertibility; they are not new assumptions.

## Coefficient map and exact finite certificate

For real or complex u,s define

    Fₓ(u,s)=det(uI+s(P(x)+Q(x))+P(x)Q(x)).

The nine-coordinate real map Φ is ordered by monomials

    (1,u,s,u²,us,s²,u²s,us²,s³),

and must satisfy, for all parameters and u,s,

    Fₓ(u,s)=u³+Σⱼ Φ(x)ⱼ monomialⱼ(u,s).

The leading u³ coefficient is exactly 1 and all coefficients are real. For an economical direct proof, put Dᵢ=u+s(pᵢ+qᵢ)+pᵢqᵢ and Sᵢ=s+pᵢ. Then prove the compact identity

    F = D₁D₂D₃ − (c²+d²)S₂S₃D₁ − b²S₁S₃D₂
        − a²S₁S₂D₃ + 2abc S₁S₂S₃.

The exact Python preflight verified this against direct six-term 3×3 determinant expansion. It is still an obligation to prove in Lean. This form avoids a general multivariate-polynomial coefficient library if Φ is defined by the resulting nine explicit polynomial expressions and the displayed identity is proved.

At x*, the coefficient vector is

    Φ(x*)=(300,159,814,24,263,697,18,103,189).

The actual derivative must be proved equal to the 9×10 matrix J recorded in SP15-JACOBIAN-PREFLIGHT.json, in the exact variable/monomial order above. It must be derived from the actual polynomial Φ; a bare nonsingular numeric matrix is not enough.

Let J₉ be its first nine columns (d is excluded). The proposed exact finite certificate is

    J₉=L U,
    L lower triangular with diagonal all 1,
    U upper triangular with nonzero diagonal,
    diag(U)=(300,39/2,−100/39,37123/1875,345081/148492,
             −147294/115027,−1401/8183,4186/37827,136/2093),
    product(diag(U))=−1088.

SP15-JACOBIAN-LU.json records the full exact rational L,U. No row permutation is needed. Prove the matrix identity and triangular properties using exact arithmetic, then use determinant multiplicativity and triangular determinant lemmas; do not expand a 9×9 determinant into 9! permutations. The actual standard-library Fraction calculation checked the reconstruction and product. These are numerical planning results, not Lean certificates.

## Local fiber with a certified free coordinate

Define G(x)=(Φ(x),d)∈ℝ⁹×ℝ. Its derivative at x* has block form [[J₉,J_d],[0,1]], hence is invertible once the previous obligations are proved. Prove the strict derivative and package the linear equivalence using finite-dimensional matrix/linear-map APIs.

Apply the real inverse-function theorem already in pinned Mathlib to obtain an actual local inverse of G. Restrict its neighborhood so the inverse remains in B. For t sufficiently close to 1, define

    ψ(t)=G_local_inverse(Φ(x*),t).

Then prove ψ(t)∈B, Φ(ψ(t))=Φ(x*), and d(ψ(t))=t. The last identity proves ψ injective. No global constant-rank theorem, unknown maximal-rank point, or smooth submanifold development is needed. Smoothness of matrix square roots and Jordan-type classification are supplementary claims in the paper, not requirements of the original finiteness question; they need not be formalized to discharge the full canonical target.

## Two essential universal transport obligations

1. For all x,y∈B with Φ(x)=Φ(y), all z:ℂ and all k<9, prove equality of the actual kth singular values of A(x)−zI and A(y)−zI. For t>0, s=t+|z|², prove the block identity

       det(tI+(A(x)−zI)*(A(x)−zI)) = t³ Fₓ(s³/t,s).

   The star on the first shifted factor is conjugate transpose. Use two Schur complements with actual invertibility, then det(sI+BC)=det(sI+CB). Polynomial identity on all positive t yields equality of the Gram characteristic polynomials. Reuse the actual Gram-to-singular-value semantics, including multiplicities, rather than replacing singular values with unordered sets.
2. For all x,y∈B, prove that any unitary similarity between A(x),A(y) forces x=y. Kernels of A and A² give the same fixed three-block flag, so the intertwiner must be block diagonal. The middle block V satisfies P(y)=V*P(x)V and Q(y)=V*Q(x)V. Because the three p intervals are disjoint, (pᵢ−pⱼ′)Vᵢⱼ=0 forces all off-diagonal entries of V to vanish without a separate permutation theorem. Unitarity makes every diagonal entry nonzero, so pᵢ=pᵢ′. Positive real a,b then force the relative phases to be 1, yielding Q(y)=Q(x), hence x=y. No general simultaneous-unitary-class theorem is assumed.

Finally choose M+1 distinct t values in the local interval, for example by affine rescaling j/(M+2). Apply both transport obligations. This produces arbitrary finite families, not merely two inequivalent examples.

## Required gates

Two independent nonauthor statement reviews, actual local statement elaboration, and an explicit freeze are required before proof implementation. No such approval, LeanCert execution, Lean compilation, Comparator run or completed-target count is asserted here. Later publication must use truthful formalization.yaml and exact original-target Comparator contracts, separate real local and GitHub records, and retain all original authorship with George Stepaniants's department/university and no email.

## Final statement-draft refinements, 17 September 2026

This document is fixed before the first SP-15 Lean definition or contract is written. All scalar definitions use exact rationals. The coordinate domain is the normed real space `Fin 10 → ℝ`, the coefficient range is `Fin 9 → ℝ`, and the augmented map is `Fin.lastCases (x 9) (coefficients x)`. Its last coordinate is exactly d; no rank assumption or chosen inverse occurs in a definition. The coefficient formulas are the nine explicit collected formulas of the compact determinant identity. The numerical Jacobian, its first-nine-column minor, and L,U are literal data; their links to the actual derivative and determinant are separate unconditional proof obligations.

For the literal original endpoint, singular values are Mathlib's decreasing singular values of Matrix.toEuclideanLin, at each index Fin n. Unitary similarity uses exactly the original one-sided condition UᴴU=I; two-sided unitarity is derived when needed. `CanonicalFiniteness` preserves both original positivity quantifiers n≥1 and M≥1 and the pair i<j. A stronger auxiliary family contract works for every natural M, including zero, but the published original target is its literal negation.

The construction is first a matrix on Fin 3 ⊕ (Fin 3 ⊕ Fin 3), then reindexed by explicit nested finSumFinEquiv to Fin 9. P,Q and their CFC.sqrt values are concrete. The block-flag statements refer to actual multiplication and actual coordinate subspaces; arbitrary unitary intertwiners, not a premade diagonal-unitary predicate, must be reduced to those blocks. Q positivity is proved on the whole open box by the strict diagonal margin 3/4. Disjoint p intervals apply to different parameter points as well as one point.

The full proof may establish only the local coefficient-fiber properties required to choose arbitrary finite subfamilies. Smoothness of the square-root map, Jordan-type classification, and an explicit numerical radius for the inverse-function neighborhood are not required by the canonical target. No lower bound on that radius is introduced as an unproved numerical assertion.

This packet is a draft: no independent approval, statement elaboration, freeze, LeanCert execution, Lean proof, Comparator run, or completed-target increment has occurred.
