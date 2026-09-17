# SP-15 exact contracts 22–26: plan before implementation

Author: /root/mi13_full_referee2. Formalization contribution: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology; substantial OpenAI Codex assistance. Preserve the canonical
mathematical authors and existing code credit. No email. This is an author
plan, not an independent review, execution receipt or completed result.

The full canonical Section3 has been read. This proof retains all arbitrary
unitaries in the original one-sided definition UᴴU=I. A block unitary is a
derived conclusion, never a hypothesis restricting the possible intertwiners.

## Numerical and algebraic statements before code

1. Every block has dimension3 and the full construction has dimension9. The
   frozen nested Sum index and blockEquiv determine its exact positions.
2. For v=(v₁,v₂,v₃), the actual blockMatrix satisfies

       Av=(R v₂,S v₃,0),       A²v=(RS v₃,0,0).

   Actual root units imply injectivity of these multiplication maps, including
   the product RS. These equations prove both exact kernel predicates in22.
3. If UᴴU=I for a finite square complex U, then UUᴴ=I by the existing finite-ring
   cancellation theorem. From A_y=UᴴA_xU derive A_xU=UA_y and reindex U to the
   same nested three-block coordinates.
4. Writing its nine actual blocks Uij, three entries of this intertwining
   identity imply

       R_x U21=0,       S_x U31=0,
       S_x U32=U21 R_y=0.

   Unit cancellation proves U21=U31=U32=0. This is the coordinate content of
   flag preservation, proved directly without 9 basis-vector expansions.
5. With U upper block triangular, the (1,1) block of UᴴU=I gives U11ᴴU11=I.
   Its (1,2),(1,3) blocks give U11ᴴU12=U11ᴴU13=0; finite-square unitarity makes
   U11ᴴ a unit, so U12=U13=0. The (2,2) block gives U22ᴴU22=I and (2,3) gives
   U22ᴴU23=0, hence U23=0. The (3,3) block then gives U33ᴴU33=I. All six
   off-diagonal blocks have been eliminated from the unrestricted original U.
6. The actual (1,2),(2,3) blocks of the original conjugacy yield

       R_y=U11ᴴR_xU22,       S_y=U22ᴴS_xU33.

   Therefore R_yᴴR_y=U22ᴴP_xU22 and S_yS_yᴴ=U22ᴴQ_xU22, using both-sided
   identities for U11 and U33 and the actual root squares. This proves24.
7. For arbitrary V from24, P_xV=VP_y. Its (i,j) entry is

       (p_i(x)−p_j(y)) V_ij=0.

   The already proved cross-point interval separation contract4 makes the
   first factor nonzero whenever i≠j. Thus V is diagonal with entries v_i and
   conj(v_i)v_i=1. This uses the fixed 1/16 box and needs no spectral sorting,
   permutation of eigenvectors, eigenvalue solver or repeated-spectrum case.
8. The (0,1),(0,2) entries of Q_y=VᴴQ_xV give

       a_y=conj(v₀)a_x v₁,       b_y=conj(v₀)b_x v₂.

   The already proved a_x,a_y,b_x,b_y>0 and |v_i|=1 imply a_y=a_x, b_y=b_x.
   Cancel these nonzero real scalars to get conj(v₀)v₁=conj(v₀)v₂=1, and compare
   with conj(v₀)v₀=1 to get v₁=v₀=v₂. Hence V=v₀I and both P and Q are fixed
   by conjugation. No argument function, trigonometric phase or root extraction
   is needed to prove the scalar-unitary conclusion.
9. Equality of P gives x0=y0, x1=y1, x2=y2. Equality of Q gives x3=y3,
   x4=y4, x5=y5 from its diagonal; x6=y6 and x7=y7 from its real top-row
   entries; and x8=y8, x9=y9 from the real and imaginary parts of entry(1,2).
   These ten exact equalities prove x=y. No coordinate is omitted.

All scalar strictness comes from the actual box bounds and separation, which
genuinely consume the established kernel-mode LeanCert certificate. No new
interval subdivisions, approximate phases or numerical matrix computations
are needed. These universal matrix identities are not certified by examples.

## Contract22: actual kernel flags

Use Matrix.fromBlocks_mulVec together with fromRows_mulVec/fromCols_mulVec to
prove the explicit three output components. Prove the block square once with
fromBlocks_multiply and the column/row partition APIs. The forward directions
use mulVec_injective_of_isUnit for R,S and their product; the reverse directions
substitute the stipulated zero components into the same actual identities.
The frozen predicates quantify all vectors on BlockIndex; do not replace them
with a different ambient or an assumed abstract flag.

## Contract23: unrestricted unitary intertwiner

Transport the given U to BlockIndex with blockEquiv.symm. Preserve unitary
products and the original conjugacy using reindex/submatrix multiplication,
one and conjugate-transpose lemmas, retaining the inverse reindex equality.
Introduce actual submatrices for its nine blocks and reconstruct U by the
existing fromBlocks_toBlocks and fromRows/fromCols reconstruction lemmas.

Apply the block identities in obligations3–5. IsUnit.mul_left_cancel cancels
the root and unitary diagonal factors. The direct intertwining route replaces
basis enumeration while proving the same flag-compatible structure described
by the canonical proof. Contract22 is still proved exactly and independently;
it is not weakened to accommodate this optimization.

Extract both root block identities from the original conjugacy, now with all
off-diagonal blocks zero, and reindex the reconstructed diagonal matrix back
to Square9. The result must be exactly U=diagonalBlocks U₁ U₂ U₃ in the frozen
definition, with all three one-sided unitary identities proved.

## Contract24: preserve the correct root-product order

Use contract23 and choose V=U₂. For P use R_yᴴR_y and cancel U₁U₁ᴴ. For Q use
S_yS_yᴴ and cancel U₃U₃ᴴ. Both become the frozen P_y and Q_y because roots are
Hermitian with their actual square identities. Using the same product order
for both without checking the block locations would be wrong; the proof will
make the two calculations explicit. No uniqueness theorem for square roots
or nonlinear transformation of the parameters is needed.

## Contract25: cross-point diagonal separation, then scalar phase

From hV derive VVᴴ=I. Multiply hP on the left by V to get the actual matrix
intertwining identity. Matrix.diagonal_mul/mul_diagonal reduce each entry to
the scalar equation of obligation7. Use p_intervals_separate x y hx hy i j
for i≠j and Complex.ofReal_injective to establish its nonzero factor. Rebuild
V as Matrix.diagonal (fun i => V i i), not just an asserted diagonal property.

The conjugate-transpose and diagonal multiplication formulas give v_iᴴv_i=1.
Norms, norm_mul, norm_conj and nonnegativity give |v_i|=1; this is a scalar
equality with no interval computation. Prove the two positive-edge equations
and cancellation as in obligation8. Then V=v₀I, and elementary scalar-matrix
algebra using conj(v₀)v₀=1 reduces hP and hQ to P_y=P_x and Q_y=Q_x.
Extract their ten parameter equalities using explicit entries and real/imaginary
parts, and use Fin10 extensionality. No sign ambiguity remains because both
specified connecting entries are strictly positive in the full box.

## Contract26 and gates

Combine contract24 with contract25 for the original UnitarySimilar predicate.
Suggested modules: KernelFlag, UnitaryBlocks, MiddleConjugacy, SliceRigidity,
UnitaryInjectivity. Root may assign different modules to separate source
authors without simultaneous editing. No implementation begins before the
coordinator accepts this source-bound plan. Existing exact headers and all
thirteen protected files remain unchanged. Root alone compiles with the
existing default limits; failed attempts remain recorded. No original-target
count or final Linux claim is made by this plan.
