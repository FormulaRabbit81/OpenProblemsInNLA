# Strict reduction: actual primary reuse

The approved plan's 17 primary-source hashes and eight project bindings were
rechecked unchanged before and after authoring. This batch realizes its steps1-9.
All detailed line/source bindings remain in schur-reduction-pair-01; no large
source snapshot is duplicated here.

SchurEnergy uses Matrix.toLpLin_one/mul_same and linearity, the exact
Matrix.toEuclideanLin_conjTranspose_eq_adjoint bridge, and
LinearMap.adjoint_inner_left. The real energy conversion has an explicit
complex-field norm_sq_eq_re_inner identity; real scalar casts use the inspected
Complex.conj_ofReal and Complex.re_ofReal_mul. It then evaluates the existing
schur_defect_identity, without a PSD assumption or a new spectral theorem.

SchurReduction uses X_mul_divX_add and coefficient-zero algebra to prove finite
Toeplitz nilpotence, then consumes the already-proved nilpotent_inverse and
its Toeplitz closure. Strict positivity of alpha follows from sq_lt_sq₀;
Complex.ofReal_ne_zero (Data/Complex/Basic.lean:141) justifies its inverse.
The concrete expression K=-conj(c)*(U-cI) equals the polynomial K proposed in
the approved plan by X*divX(p)+C(c)=p; its proof is through the same coefficient
zero and nilpotence route.

Actual Euclidean norm bounds and euclidean_norm_attainment prove ||Z||=1.
The active-block theorem transfers that boundary norm to the smaller block.
The final full-subspace equivalence uses maximal_space_norm and nonnegative
square comparison directly; zero vectors are included. No source assumes a
maximal singular vector, inverse, rank, or desired kernel equality.

Public Toeplitz subtraction/scalar/commutation helpers and the norm-one
maximal-space characterization are available for the approved pair step.
No resource settings, definitions, frozen headers or trust mode changed.
