# Proposed implementation of frozen Schur contracts 12 and 14

PLAN ONLY. Root acceptance is required before writing the new proof modules.
The numerical and semantic obligations were recorded first in file00. The
exact frozen headers are bound separately, without modifications.

Write T_r(q)=toeplitz r q and L_A=euclideanLin A. Every norm below is the
frozen actual Euclidean norm or its induced operator norm. For contract12,
set N=n+2, U=T_N(p), c=p.coeff0, alpha=1-||c||^2 in R, alphaC=(alpha:C),
W=U-cI, M=I-conj(c)U. Do not identify the arbitrary symbol p with a truncated
or constant polynomial.

## 1. Strict reduction: concrete inverse and exact defect

1. From ||c||>=0 and ||c||<1 obtain alpha>0, then alphaC!=0. The only scalar
   inverse used in this contract is alphaC^(-1). In particular c=0 is allowed.

2. Use X*divX(p)+C(c)=p. Put
   r=C(-conj(c))*divX(p), K=T_N(X*r).
   Toeplitz algebra and c*conj(c)=((||c||^2:R):C) give M=alphaC I+K.
   Prove K^N=0 inside the commutative polynomial algebra before mapping it:
   T_N((X*r)^N)=T_N(X^N)*T_N(r^N)=0. This uses the existing shift nilpotence,
   not triangular eigenvalues or an infinite geometric series.

3. Choose B=finiteInverse alphaC K. The already-proved nilpotent_inverse gives
   M*B=B*M=I and IsToeplitz B. The product Z=W*B is Toeplitz by the existing
   algebra hom. Its polynomial symbol has zero constant coefficient because
   p-C(c) does; hence every diagonal entry is zero. Also Z*M=W directly from
   B*M=I. Both inverse identities will be exported exactly as frozen.

4. Establish one reusable matrix energy identity, using the actual linear map:
   re <L_(A^H A) x,x> = ||L_A x||^2.
   Matrix.toEuclideanLin_conjTranspose_eq_adjoint and toLpLin_mul_same identify
   the Gram action; LinearMap.adjoint_inner_left and the explicitly typed
   norm_sq_eq_re_inner (field C) finish the identity.

5. Apply x, then re <.,x>, to the existing schur_defect_identity:
   M^H M-W^H W=alphaC (I-U^H U).
   Map subtraction/scalars through Matrix.toLpLin and use the preceding
   energy identity. For real scalar casts use Complex.conj_ofReal and
   Complex.re_ofReal_mul, with an explicitly typed local identity
   re <x,x>=||x||^2. This avoids the generic-RCLike/explicit-Complex rewrite
   mismatch already encountered and repaired in MaximalSpace.
   Finally substitute Z*M=W to obtain, for EVERY x including zero,
   ||L_M x||^2-||L_Z(L_M x)||^2
     =alpha*(||x||^2-||L_U x||^2).
   No commutation involving adjoints is used.

## 2. Strict reduction: contractivity, boundary norm and full transport

6. ||U||=1 and the standard application bound give ||L_U x||<=||x||.
   For arbitrary y apply the defect at x=L_B y; M*B=I makes L_M x=y.
   Nonnegativity of the right side gives ||L_Z y||^2<=||y||^2. Compare
   nonnegative squares, then apply opNorm_le_bound to prove ||Z||<=1.

7. The existing euclidean_norm_attainment at N>=2 supplies x with ||x||=1
   and ||L_U x||=1. Thus x!=0. Put y=L_M x; B*M=I implies y!=0. The defect
   gives ||L_Z y||=||y||. The operator-norm bound then implies
   ||y||<=||Z||*||y||, so 1<=||Z|| because ||y||>0. Together with step6 this
   proves ||Z||=1. This is the attained singular endpoint; no perturbation
   to a strict contraction or simple-singular-value assumption is introduced.

8. Apply the exact schur_active_block theorem to the Toeplitz zero-diagonal
   contraction Z. It gives ||activeBlock Z||=||Z||=1. All append/prepend
   coordinate formulas are taken from that theorem and its small helpers.

9. Use maximal_space_norm for U and Z, with their norms both one. Membership
   is norm equality. By the defect and alpha>0,
   ||L_U x||^2=||x||^2 iff ||L_Z(L_M x)||^2=||L_M x||^2.
   Nonnegative-square comparison gives exactly
   x in maximalSpace U iff L_M x in maximalSpace Z.
   This proves the full frozen kernel transport, including the zero vector
   and every maximal-singular-value multiplicity. It does not redefine the
   frozen kernel in terms of the desired norm equality.

## 3. Pair step: use the supplied inverse and reconstruct scalar polynomials

For contract14 put R=n+1, N=n+2, V=activeBlock Z, and extract every old
SchurPair clause for (d,a,b). Then d<=n. Write
   A=C(c)*b+X*a, D=b+C(conj(c))*X*a, m=n-d.
Here A,D are the precise frozen schurNumerator/schurDenominator; D is not a
matrix inverse and is not silently divided out.

10. Invoke the proved strict reduction, obtaining its concrete inverse B0.
    The supplied B equals B0 by the two inverse identities:
    B=B*(M*B0)=(B*M)*B0=B0.
    Transfer the Toeplitz, zero-diagonal, norm and maximal-space properties
    to this exact supplied B. This is necessary because contract14 does not
    separately assume IsToeplitz B. Keep its literal hleft/hright/hV/hpair
    hypotheses; hV gives the smaller norm equality directly where needed.

11. Prove d+1<N. Since degree(a)=d, degree(X*a)=d+1. On the other hand,
    degree(C(c)*b)<=degree(b)<=d, including c=0. Thus the strictly lower
    degree term cannot cancel: degree(A)=d+1. The denominator has degree
    <=d+1 and D.coeff0=b.coeff0=1. Use extended polynomial degrees throughout;
    convert natural casts with Nat.cast_add when required, as in the accepted
    weighted-coefficient repair. Do not exclude zero parameter polynomials.

12. Establish two polynomial identities by ring algebra:
    D-C(conj(c))*A=C(alphaC)*b,
    A-C(c)*D=C(alphaC)*X*a.
    They are also the exact identities later used for matrix pullback.

13. Coprimality has an explicit Bezout proof. The identity
    X*divX(b)+1=b shows IsCoprime X b, with witnesses -divX(b),1.
    Combine with the old IsCoprime a b using IsCoprime.mul_left to get
    u*(X*a)+v*b=1. If t=C(alphaC^(-1)), then the new witnesses are
    t*(u-v*C(conj(c))) and t*(v-u*C(c)). Substitution of step12 makes their
    linear combination of A,D equal to t*C(alphaC)=1. No root/gcd oracle,
    divisibility cancellation by a possibly zero polynomial, or assumption
    of simple roots is used.

14. Prove the scalar identity for arbitrary complex c,s,t:
    ||s+conj(c)*t||^2-||c*s+t||^2
      =(1-||c||^2)*(||s||^2-||t||^2).
    Complex.sq_norm, normSq_add, normSq_mul, normSq_conj and conjugation's
    multiplication law reduce this to real ring algebra; the two cross terms
    coincide by commutativity in C. This is a symbolic norm identity, not a
    numerical certificate.

15. Fix ||z||<=1. The old pair gives b(z)!=0 and ||a(z)||<=||b(z)||;
    hence ||z*a(z)||<=||b(z)||. Apply step14 with s=b(z), t=z*a(z), and
    alpha>0 to prove ||A(z)||<=||D(z)||. If D(z)=0, then
    ||b(z)||=||c||*||z*a(z)||<=||c||*||b(z)||<||b(z)||,
    a contradiction since b(z)!=0. This proves nonvanishing on the CLOSED
    disk, not only the open disk. For ||z||=1 the old boundary equality makes
    the right side of step14 zero; nonnegative-square comparison gives the
    required boundary equality. This route still works at c=0 and z=0.

## 4. Pair step: finite interpolation lift and untruncated parameter vectors

16. Prove small explicit finite coefficient helpers in the new modules:
    - If q.coeff0=0, then q=X*divX(q) and
      activeBlock(T_(r+1)(q))=T_r(divX(q)). The coordinate calculation is
      exactly the zero-diagonal divX calculation used in SchurActiveBlock.
    - T_r(s)=T_r(t) implies T_(r+1)(X*s)=T_(r+1)(X*t). Coefficient0 is zero;
      for coefficient j+1, compare column0 at index j of the smaller matrix.
      A positive-index branch supplies a valid column0 even if the helper is
      stated for r=0. There is no inference of polynomial equality from
      equality of finite Toeplitz matrices.
    These helpers are proved entrywise with coeff_divX/coeff_X_mul, rather
    than importing a hypothetical truncation or compression theorem.

17. Choose a symbol q for Z; q.coeff0=0 follows from its zero diagonal at
    0:Fin N. The old matrix interpolation V*T_R(b)=T_R(a), step16 and
    Toeplitz multiplication give
    Z*T_N(b)=T_N(X*a)=S*T_N(a), where S=shift N.
    All polynomial coefficients of order N or higher remain irrelevant.

18. M and W commute because both are explicit Toeplitz polynomials; prove
    this using T(s)T(t)=T(st)=T(ts)=T(t)T(s), not a blanket commutativity
    assertion about matrices. Therefore M*Z=W*M*B=W. Multiplying step17 on
    the left by M and expanding M=I-conj(c)U yields
    U*(T_N(b)+conj(c)*S*T_N(a))=c*T_N(b)+S*T_N(a).
    These are exactly U*T_N(D)=T_N(A), the new interpolation clause.
    No adjoint is commuted through any Toeplitz factor.

19. From the new interpolation and step12 get the matrix pullback
    M*T_N(D)=alphaC*T_N(b).
    Toeplitz action plus coeffVector_mul_truncate converts these two matrix
    equalities into, for every polynomial h,
    L_U(coeffVector N (D*h))=coeffVector N (A*h),
    L_M(coeffVector N (D*h))=alphaC • coeffVector N (b*h).
    These coefficient-vector identities themselves need no degree bound on
    h; retain the frozen bound for the exported action clause. Scalar/addition
    identities for coeffVector follow directly by PiLp.ext.

20. For DegreeLE h m, extended-degree multiplication gives
    DegreeLE (b*h) n and DegreeLE (a*h) n,
    DegreeLE (D*h) (n+1) and DegreeLE (A*h) (n+1).
    Thus coeff (b*h) (n+1)=0, giving the exact coordinate identification
    coeffVector N (b*h)=appendVector (coeffVector R (b*h)) 0.
    Prove this by Fin.lastCases/Fin.snoc coordinates and the degree-to-zero
    coefficient theorem. This is where the distinction between R and N
    matters; no unrestricted truncation is identified with a polynomial.

## 5. Pair step: both maximal-space inclusions and dimension

21. From the strict transport and the active-block saturation formula obtain
    y in maximalSpace Z iff y=appendVector(g,0) for some g in maximalSpace V.
    Use exists_appendVector for arbitrary y, and maximal_space_norm together
    with ||Z||=||V||=1. Both directions include zero.

22. If x is in maximalSpace U, apply step21 to y=L_M x. The old pair supplies
    h with DegreeLE h m and g=coeffVector R(b*h). Step20 identifies
    L_M x=coeffVector N(b*h). Set h'=alphaC^(-1) • h; degree_smul_le preserves
    DegreeLE h' m, even when h=0. By step19,
    L_M(coeffVector N(D*h'))=coeffVector N(b*h)=L_M x.
    The left inverse L_B cancels L_M, proving x=coeffVector N(D*h').

23. Conversely let x=coeffVector N(D*h) with DegreeLE h m. By the old pair,
    g=coeffVector R(b*h) lies in maximalSpace V. Step21 puts appendVector(g,0)
    in maximalSpace Z, and the submodule is closed under alphaC-scaling.
    Steps19-20 identify this scaled vector with L_M x; strict transport then
    proves x is in maximalSpace U. This gives exactly the new existential
    parameterization, while step19 already supplies its action clause.

24. Derive dimension through explicit inverse linear maps, rather than
    postulating injectivity of polynomial multiplication or a rank formula.
    Package J(g)=appendVector(g,0) and P(y)_i=y_(i.castSucc) as complex linear
    maps. Their linearity and P*J=id are coordinate identities. Define
    F:maximalSpace U -> maximalSpace V by F(x)=P(L_M x),
    G:maximalSpace V -> maximalSpace U by G(g)=L_B(J(g)).
    Steps9 and21 justify their restricted codomains. M*B=B*M=I, P*J=id,
    and L_M x=J(P(L_M x)) for x in maximalSpace U prove F*G=id and G*F=id.
    Use LinearMap.restrict (or domRestrict/codRestrict), then the pinned
    nondeprecated LinearEquiv.ofLinearMap and LinearEquiv.finrank_eq.
    The old SchurPair's proved dimension gives
    finrank(maximalSpace U)=finrank(maximalSpace V)=(n+1)-d
      =(n+2)-(d+1).
    The entire spaces are isomorphic, so repeated maximal singular values
    are retained. The only smaller rank fact used is its explicit inductive
    SchurPair clause, not an additional oracle hypothesis.

## Proposed module boundaries, checks and remaining risks

SchurReduction.lean imports the existing NilpotentInverse, SchurDefect,
NormAttainment, MaximalSpace and SchurActiveBlock foundations. It proves its
small generic matrix/energy helpers and exact contract12, with axiom printing
and kernel trust assertion. Seal this bounded module first for the root's
serial compiler queue. SchurPairStep.lean then imports it and proves the
scalar/polynomial/coordinate helpers and exact contract14. Root owns all
compiler runs. No JordanReversal or PolynomialTransport source is touched.

Neither new source exists yet. The active-block dependency passed actual
root local88; its exact source/receipt bindings are recorded. Endpoint is not
a dependency of these two contracts; its source separately passed actual90.

No paper-level obstacle has appeared in this derivation. The pair step is
substantially larger than the strict reduction: likely elaboration issues are
the Euclidean adjoint/scalar wrappers, WithBot degree casts, finite index casts
in the interpolation lift, and subtype coercions in the final linear
equivalence. They must be repaired within these exact statements. No proof of
finite_schur_boundary, scaled_maximal_factorization or the final canonical
target is claimed by this two-contract plan.

All 13 frozen inputs, exact contract headers, pins, trust settings, original
mathematical/library credits and George Stepaniants' Caltech CMS attribution
without email remain fixed. No new interval computation or LeanCert certificate
is proposed. Independent proof review and actual local elaboration are still
required; no GitHub Comparator run or counting change occurs here.
