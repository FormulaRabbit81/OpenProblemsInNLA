# Proposed exact finite-boundary and scaling implementation

PLAN ONLY. Root acceptance is required before writing either new module.
The numerical/semantic obligations were recorded first in file00. Preserve
all13 frozen inputs and both literal theorem headers. Suggested modules:
FiniteSchur.lean for15 and ScaledFactorization.lean for16, with only small
shared scalar norm helpers if needed under the existing resource limits.

## Contract15: terminating finite dimension induction

1. Induct on the natural dimension n with the complete proposition
   forall hn:1<=n, forall U:Square n, IsToeplitz U -> operatorNorm U=1 ->
   exists d a b, SchurPair n U d a b. The zero case is contradictory to hn.
   Strong natural induction (Nat.strong_induction_on) is available, or
   ordinary induction with all dimension-dependent data generalized.
   The recursion is structural on the positive finite dimension, never on
   singular-value multiplicity or a limiting sequence.

2. Extract an actual polynomial witness p from IsToeplitz U and substitute
   U=T_n(p). This does not restrict p.degree or identify p with a truncation.
   In the n=1 case, schur_dimension_one p and the given norm1 equality imply
   ||p.coeff0||=1. Invoke schur_scalar_endpoint with hn=1 to obtain the
   complete SchurPair at d=0,a=C(p.coeff0),b=1. All11 clauses are reused.

3. For n>=2 write n=m+2, using successor cases to avoid any matrix-index
   equivalence beyond definitional natural arithmetic. The diagonal bound
   schur_diagonal_bound gives ||p.coeff0||<=1. Split on equality to1.
   If equality holds, schur_scalar_endpoint immediately supplies the same
   complete d=0 pair in the current dimension. No claim is made that p is
   a constant polynomial; only the finite matrix is scalar.

4. In the remaining case the real inequality is strictly <1. Apply
   schur_strict_reduction p hnorm hc to obtain its concrete B, both inverse
   identities, Toeplitz Z, zero diagonal, ||Z||=1 and ||activeBlock Z||=1.
   Obtain IsToeplitz(activeBlock Z) from the first component of
   schur_active_block Z hZ hdiag (le_of_eq hZnorm). This is a proved actual
   finite Toeplitz witness; do not assume arbitrary matrix compressions are
   Toeplitz. No new symbol or degree hypothesis is introduced.

5. The active dimension m+1 is positive and strictly below m+2. Invoke the
   induction hypothesis on activeBlock Z with the preceding Toeplitz and
   norm proofs. This produces some d,a,b with the complete smaller pair.
   Apply exact schur_pair_step p a b B hnorm hc hleft hright hV hpair.
   Return d+1, the frozen schurNumerator and schurDenominator. Their exact
   degree, nonzero closed-disk denominator, coprimality, matrix action,
   entire maximal space and dimension are all supplied by contract14.
   Dimension strictly decreases at every recursive call, so termination
   reaches the actual dimension1 endpoint. c=0 uses the strict branch.

6. No direct numerical certificate, recursive denominator oracle, SVD,
   assumption of distinct singular values, new axiom or changed definition
   is needed. Keep literal contract15 and its trust/axiom assertions.

## Contract16: normalize the actual operator norm and transport the kernel

7. Put M=operatorNorm T, a real scalar. euclidean_norm_attainment hn T
   supplies M>=0 and (M=0 iff T=0). Together with hne obtain M>0, hence
   M!=0 and (M:C)!=0 via Complex.ofReal_ne_zero. This is proved positivity
   of the actual induced Euclidean norm, not an assumption on the entries
   or positive definiteness. No inverse is used before this step.

8. Establish the small actual-map identity
      euclideanCLM(c•T)=c•euclideanCLM(T)
   by ContinuousLinearMap.ext and the proved euclideanLin_smul_apply.
   A documented change exposes only the existing continuous wrapper.
   The generic norm_smul, applied to this ContinuousLinearMap normed space,
   gives operatorNorm(c•T)=||c||*operatorNorm T. Do not apply a norm formula
   directly to Matrix with its unrelated ambient norm instance.

9. Set s=(M:C)^(-1), U=s•T, exactly as frozen. If T=T_n(p), then
   U=T_n(s•p) by toeplitz_smul; thus IsToeplitz U has an explicit witness
   and arbitrary high coefficients remain permitted. norm_inv and
   Complex.norm_of_nonneg turn ||s|| into M^(-1). By M!=0,
   operatorNorm U=M^(-1)*M=1. Apply contract15 to obtain d,a,b and the
   complete SchurPair n U d a b; retain that proof unchanged for the first
   result conjunct.

10. Scalar cancellation gives T=(M:C)•U. From euclideanLin_smul_apply and
    Complex.norm_of_nonneg obtain, for every x including zero,
      L_T x=(M:C)•L_U x,
      ||L_T x||=M*||L_U x||.
    Apply maximal_space_norm to T and maximal_space_norm_one to U.
    Their kernel memberships are respectively ||L_T x||=M*||x|| and
    ||L_U x||=||x||. Substitute the norm scaling identity and cancel the
    nonzero REAL factor M using mul_left_cancel₀ for the forward direction;
    the reverse is direct substitution. Hence exactly
      x in maximalSpace T iff x in maximalSpace U.
    This treats the entire repeated maximal singular space, without
    developing or assuming an adjoint scaling/rank oracle.

11. Compose that membership equivalence with the supplied pair's parameter
    clause. The same h, the same bound DegreeLE h(n-1-d), and the same b*h
    coefficient vector result; no variable is rescaled. Retain zero h and
    all allowed complex coefficients.

12. For every h with the exact frozen degree bound, use the pair's action
    L_U(coeffVector n(b*h))=coeffVector n(a*h), then multiply by (M:C)
    through the identity in step10. This gives literally
      L_T(coeffVector n(b*h))=(operatorNorm T:C)•coeffVector n(a*h).
    Assemble all three frozen result conjuncts and print/assert kernel
    trust. All scope restrictions remain precisely n>=1, IsToeplitz T,
    T!=0. No new computation or certificate is required.

## Execution and review boundary

Both modules are UNWRITTEN at this plan seal. Contract14 is an exact sealed
candidate in the root's actual104 queue; implementation of this plan must
reuse only its source-matched successful output after any observed repair.
Root alone runs one local compiler, one thread, 4096MiB and unchanged default
limits. No compiler/cache/Git/network action occurs in this author plan.
Independent complete proof review and the final real GitHub Comparator are
separate later requirements. Neither this plan nor partial local successes
complete or count the original IE02 target.
