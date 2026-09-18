# Proposed strict and weighted scalar factorization implementation

PLAN ONLY. Require root plan acceptance and actual success of prerequisite26
before implementation. The exact frozen inventory is: WeightedFold21,
CommonCircleRoot22, Fourier23, EffectivePolynomial24, reciprocal pairing25,
inside factor26, strict scalar27, weighted scalar28. Root and another author
own25/26; this plan neither implements nor assumes an unproved oracle for them.

Suggested two small modules: StrictFactorization.lean contains a shared circle
reflection-square helper and exact27; WeightedFactorization.lean contains an
unweighted common-root induction helper and exact28. Splitting the induction
helper into a third module is permissible only as a resource-preserving source
organization choice with the same accepted contracts and default limits.

## A. Shared fixed-bound circle identity

1. For degree(p)<=r and |z|=1, establish once
      (p*conjReflect r p).eval z = z^r * (|p.eval z|^2:C).
   Prove z!=0 from |z|=1, use reflection_evaluation's second conjunct, then
   Polynomial.eval_mul. Reassociate the complex scalar factors and use
   Complex.mul_conj together with Complex.sq_norm. No expansion of reflection
   coefficients or natDegree substitution is needed. This helper is used by
   BOTH strict normalization and the final weighted polynomial equality.
   It remains valid for zero p, r=0 and a degree bound larger than degree(p).

## B. Strict27: identify the complex multiplier and rescale by a REAL square root

2. Apply effective_factor_polynomial to m,q,hq,hno. It supplies ell<=m,
   P=effectivePolynomial m ell q with exact degree2ell, nonzero coefficient0,
   its fixed-bound self reflection, and for every circle z,
      P(z)=z^ell*(Q(z):C), P(z)!=0,
   where Q=sumSquares q. These are the actual polynomial and actual family;
   do not replace either by a symbol with an assumed Fourier representation.

3. Invoke the completed exact reciprocal_inside_factor26 with those supplied
   hypotheses. Put h0=rootProduct(insideRoots P). Obtain its exact degree ell,
   nonzero evaluation0, no circle roots, and a complex kappa!=0 with
      P=C kappa*(h0*conjReflect ell h0).
   Contract26 is stated for every ell, including0. Its independent author
   confirmed that empty root multisets and ell=0 are in scope. Consume that
   unconditional theorem uniformly: ell=0 means h0=1, so this route produces
   a positive constant factor without an additional ell>=1 assumption.
   Do not reprove any root pairing, multiplicity, multiset or product theorem.

4. Evaluate that polynomial equality on the circle and use step1 at bound ell.
   Comparing with step2 gives
      z^ell*(Q(z):C) = z^ell*(kappa*(|h0(z)|^2:C)).
   Since z!=0, pow_ne_zero gives z^ell!=0, even ell=0. Cancel this factor with
   mul_left_cancel₀ to obtain the full complex identity
      (Q(z):C)=kappa*(|h0(z)|^2:C).
   No division by h0(z) is needed at arbitrary circle points.

5. Specialize to z=1. Existing sumSquares_pos, with hno at1, gives Q(1)>0.
   The supplied no-circle-root property gives h0(1)!=0, hence
   R=|h0(1)|^2>0 by norm_pos_iff and sq_pos_of_pos. Thus (R:C)!=0.
   Define beta=Q(1)/R in R; div_pos gives beta>0. Applying eq_div_iff to the
   z=1 identity and using Complex.ofReal_div proves
      kappa=(beta:C).
   This establishes both reality and strict positivity of the actual complex
   multiplier. Do not silently replace kappa by its real part or its norm,
   and do not choose a complex square root.

6. Substitute kappa=(beta:C) into step4, use Complex.ofReal_mul and injectivity
   of the real embedding to get Q(z)=beta*|h0(z)|^2 on the entire circle.
   Exact degree(h0)=ell and ell<=m imply DegreeLE h0 m, with explicit WithBot
   casts. Define h=weightedFold beta h0=C(sqrt(beta):C)*h0.

7. Reuse weighted_fold21 on the SINGLETON family Fin1, constant polynomial h0
   and constant weight beta. Its degree clause supplies DegreeLE h m, and
   Fin.sum_univ_one specializes its evaluation clause to
      |h(z)|^2=beta*|h0(z)|^2.
   This reuses the already-proved real sqrt and complex scalar norm bridge
   instead of duplicating it. Together with step6 it proves exact27. The
   strict empty-family case is inconsistent only through hno itself; no
   nonempty-family hypothesis is added to the theorem.

## C. Unweighted weak factorization by common-circle-root degree induction

8. Prove a small helper for EVERY l,m,q with DegreeLE(q_j)m, requiring no hno:
      exists h, DegreeLE h m and forall circle z, |h(z)|^2=sumSquares q z.
   Use natural strong induction on m, with l and the entire family and its
   degree hypotheses generalized. This is a finite structural proof, not a
   perturbation or limiting argument.

9. If every q_j=0, choose h=0. Extended degree is bottom and the sum is0.
   This includes the empty family, allzero weights after folding, and m=0.
   In the complementary case obtain an actual j with q_j!=0. Split on the
   exact hno proposition. If it holds, use the now-proved strict27 directly.

10. Otherwise classical negation of hno gives a circle point zeta where every
    q_j(zeta)=0. Call exact common_circle_root_reduction22 using the supplied
    degree bounds and the nonzero-polynomial witness from step9. It gives
    m>=1 and a family r_j with
      q_j=(X-C zeta)*r_j, DegreeLE(r_j)(m-1).
    Therefore m-1<m. Apply the induction hypothesis to this actual quotient
    family and obtain r of degree<=m-1 with the corresponding circle identity.
    Set h=(X-C zeta)*r. Polynomial.degree_X_sub_C and degree_mul_le_of_le give
    degree(h)<=1+(m-1)=m, including r=0. Normalize WithBot additions with
    explicit casts and Nat.cast_add, as in the earlier accepted degree repairs.

11. For every circle z, evaluation of the products and norm_mul/mul_pow give
      |h(z)|^2=|z-zeta|^2*sum_j|r_j(z)|^2=sum_j|q_j(z)|^2.
    Move the common real factor through the finite sum by Finset.mul_sum.
    No cancellation of z-zeta occurs, so the identity includes z=zeta itself.
    Repeated circle roots trigger the same branch as many times as necessary;
    the decreasing natural degree bound proves termination. There is no
    assumed even-multiplicity or real-analytic zero theorem. At m=0, a common
    root of a nonzero input would contradict the m>=1 output of22.

## D. Weighted28 and the exact fixed-bound polynomial identity

12. Form the actual family q'_j=weightedFold(w_j)(q_j). weighted_fold21 gives
    its degree bounds and sumSquares q' z=sum_j w_j*|q_j(z)|^2 for every z.
    Apply the weak helper to q' and m. Its h has DegreeLE h m and the desired
    weighted norm identity. All zero weights are handled by that concrete
    real-square-root definition and the allzero branch, without imposing
    circle-root conditions on the corresponding original q_j. No weight-sum
    normalization is required.

13. To prove the final polynomial identity, invoke circle_polynomial_uniqueness20
    on the two polynomials displayed in the frozen contract. At every circle z,
    step1 identifies the left evaluation with z^m*(|h(z)|^2:C). Apply the SAME
    step1 to every original q_j with its given bound m. Polynomial.eval_finsetSum,
    eval_C and eval_mul identify the right evaluation with
      sum_j (w_j:C)*(z^m*(|q_j(z)|^2:C))
        =z^m*((sum_j w_j*|q_j(z)|^2):C).
    Use Finset.mul_sum and Complex.ofReal_sum/ofReal_mul for the last equality.
    The norm equality from step12 makes both evaluations equal, and the actual
    infinite circle gives equality of polynomials. Use the fixed bound m even
    when h or any q_j has smaller degree or is0. Do not infer equality from
    finitely many samples, replace reflection by reversal at actual degree,
    or assume the target polynomial identity as an additional hypothesis.

14. Assemble the exact weighted28 header and its three result clauses, with
    #print axioms and #assert_trust kernel on both exports. The construction
    is entirely symbolic and degree preserving. Existing kernel LeanCert
    descent data remain unchanged; no interval or numerical certificate is
    added to this route. Root alone performs actual local checks after plan
    approval and prerequisite success; source authors do not compile or
    mutate caches. Independent proof reviews and real GitHub Comparator are
    later separate requirements, and neither target is counted complete by
    this plan or by partial module success.
