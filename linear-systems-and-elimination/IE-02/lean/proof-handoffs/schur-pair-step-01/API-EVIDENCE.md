# Assembly evidence for exact frozen Schur pair-step14

The complete numerical/symbolic route was approved before source creation in
schur-reduction-pair-01 and root plan acceptance 7ea0f26e9a4d77c109a13e6fa25c1e608a143f37b46426beb5aee1995ea0fafc.
The split pre-code files retained here predate all three pair source modules.

The supplied inverse B is identified with the strict reduction inverse by
B=B*(M*B0)=(B*M)*B0=B0. No IsToeplitz B hypothesis is added. The matrix
interpolation uses the finite X-lift and commutes only the two proved
Toeplitz polynomial factors M and U-cI; it never commutes adjoints.
Mathlib Data/Matrix/Mul (Matrix.smul_mul, Matrix.mul_smul) handles the exact
scalar products. The matrix pullback is the polynomial identity D-conj(c)A
=alpha*b, evaluated by the existing Toeplitz algebra hom.

The existing toeplitz_action and coeffVector_mul_truncate give polynomial
vector action for every parameter polynomial. The degree product bound is
needed for the append-zero identity in maximal-space membership. Forward
transport replaces h by alpha^(-1)•h, preserving extended degree, and cancels
M using the supplied B. Reverse transport uses submodule scalar closure.
The already-drafted coordinate helper builds an explicit LinearEquiv of the
full maximal subspaces, giving the frozen dimension clause without a rank
oracle. All11 SchurPair clauses are assembled literally; c=0, repeated
maximal singular values and arbitrary high coefficients of p remain allowed.

Primary imports and all project source closure hashes are retained in
HANDOFF.json. SchurPolynomial02 passed actual101; SchurCoordinates02 is the
bounded failed101 repair, still awaiting root serial retry at this seal.
This assembly is UNRUN and has no independent proof review or Comparator
result. No compiler, cache, Git, network or interval computation ran here.
