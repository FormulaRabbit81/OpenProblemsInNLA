# Exact obligations before new Lean code

Status: proposed definitions and proof obligations for feasibility review only. There is no new Challenge file, proof implementation, freeze or claimed elaboration. The two future independent statement reviews must cover these full obligations and the original canonical source correspondence.

## MF-05 definitions and full target

For every natural `d >= 1`, use `Square d = Matrix (Fin d) (Fin d) C` and `EuclideanVector d = EuclideanSpace C (Fin d)`. Reuse the published MF-07 definition `spectralNorm A = norm(Matrix.toEuclideanCLM A)`. A family is any nonempty compact set of such matrices, not an array or a finite set.

Let `a_n(M)` be the maximum spectral norm of all length-n products, with the empty product equal to the identity. Let `rhoInf(M) = inf {a_n(M)^(1/n) : n >= 1}` as in MF-07. The new general semantics obligation proves that the root sequence converges to this actual value for every eligible family, including radius zero. It then exactly matches the canonical definition of joint spectral radius by a limit.

Define `dH(M,N)` as the Hausdorff distance of the images of M and N under `Matrix.toEuclideanCLM`, with the operator-norm metric on continuous linear maps. Prove this is the canonical maximum of the two sup-inf spectral distances. Do not silently use an unrelated default matrix norm. Compactness, image injectivity, nearest-point existence and finite Hausdorff distance are part of the wrapper proofs.

The final assertion is:

```
forall d >= 1, forall nonempty compact M0 subset C^(d*d),
  exists r > 0, exists C > 0,
    forall nonempty compact M,N subset C^(d*d),
      dH(M,M0) < r and dH(N,M0) < r ->
      abs(rhoInf(M)-rhoInf(N)) <= C * dH(M,N)^(1/d).
```

The intended stronger intermediate estimate is, for every `L > 0` and every two such families satisfying `norm(A) <= L` for all members,

```
abs(rhoInf(M)-rhoInf(N))
  <= d*(2*d+1) * L^(1-1/d) * dH(M,N)^(1/d).
```

Every real power has an explicit nonnegative base; the exponent uses the real coercion of positive d. The `d=1`, `dH=0`, `rhoInf=0`, and arbitrary compact/reducible cases are retained. The sharp scalar constant and sharpness examples are not additional canonical targets.

### MF-05 proof obligations in order

1. **Only fixed scalar certificate:** `(0:R) < 1/2` and `(1/2:R) < 1`, proved using pinned `interval_decide (trust := kernel)`. Consume it in the final half-radius choice and common norm-ball bound; an unused imported certificate is insufficient. No higher-dimensional interval boxes are proposed.
2. **General scalar and finite-word semantics:** `0 <= rhoInf(M) <= familyNorm(M)`; monotonicity under inclusion; for `c>0`, growth of `cM` equals `c^n a_n(M)` and `rhoInf(cM)=c*rhoInf(M)`. Positive scalar-image compactness and attainment must be actual proofs.
3. **General exponential envelope:** for every `a>rhoInf(M)` (hence `a>0`), there is `K>=1` such that `a_n(M)<=K*a^n` for every n. Choose a positive k whose root is below a using the defining infimum. Write `n=q*k+r`, use submultiplicativity and the published repeated-block lemma, and bound the finite remainders by `K=max(1,max_{r<k} a_r(M)/a^r)`. Zero products require no logarithm or division by growth.
4. **Full root semantics and growth-to-radius transfer:** use the preceding envelopes and `K^(1/n)->1` to prove convergence to `rhoInf`. Also prove any bound `a_n(M)<=K*b^n`, with `K>=1,b>0`, implies `rhoInf(M)<=b`. This is not the radius-one theorem renamed.
5. **Adjoining scalar identities:** for `e>0`, prove `rhoInf(M union {e*I})=max(rhoInf(M),e)`. A word over the union compresses to a word of M times the scalar `e^(number of identity choices)`; conversely the all-identity word and words of M give the lower bounds. Use a general exponential envelope to prove the upper bound and let its positive excess decrease to zero. A member that equals `e*I` can be assigned either valid provenance, with a deterministic case split. Preserve order of the remaining word.
6. **General quantitative comparison:** for every `L>0` bounding all generator norms, `s>=1` and `n>=0`, prove
   `a_n(M) <= d*s^(d-1) * (rhoInf(M)+2*d^2*L/s)^n`.
   If `rhoInf(M)>0`, apply the exact published radius-one comparison to `M/rhoInf(M)` and scale back. If the radius is zero, apply that same argument to `M union {e*I}`, with `0<e<=L`, and let e decrease to zero. Use inclusion to compare word maxima. This path reuses the existing difficult theorem unchanged and never assumes Hölder continuity to obtain the generalization.
7. **Controlled comparison norm:** for `u=rhoInf(M)+2*d^2*L/s>0`, the actual discounted-word envelope gives a complex norm p satisfying `norm(v)<=p(v)<=d*s^(d-1)*norm(v)` and `p(A*v)<=u*p(v)` for every A in M. Reuse MF-07's general `ProductEnvelope` lemmas; they already take an arbitrary positive discount and a supplied exponential bound.
8. **Hausdorff transfer:** for `delta=dH(M,N)`, nearest generators and norm subadditivity give `p(B*v)<=(u+d*s^(d-1)*delta)*p(v)` for every B in N. Iterate over actual words and use the actual radius transfer in item 4. Repeat with M and N reversed.
9. **Optimization:** if `0<delta<=L`, choose `s=(L/delta)^(1/d)>=1`, prove `s^d=L/delta`, and simplify
   `2*d^2*L/s+d*s^(d-1)*delta = d*(2*d+1)*L/s`.
   Then prove `L/s=L^(1-1/d)*delta^(1/d)`. These are symbolic real-power/field identities, not numerical sampling. If delta=0, the compact spectral images coincide. If delta>=L, use both radii in `[0,L]`.
10. **Local constants:** for arbitrary M0, `L=familyNorm(M0)+1>0`, `r=1/2`, and the displayed global C are positive. Nearest points in M0 and the certified `r<1` put both nearby families in the common L-ball. This gives the exact two-family original target.

## NM-04 definitions and full target

For all positive natural m,n, use actual `Matrix (Fin m) (Fin n) R` and entrywise strict positivity. Use 0-based Lean indices only through a documented bijection with the canonical 1-based indices. The distinguished row and column are the first ones. Define balanced matrices by every row sum equal to 1 and every column sum equal to `rho=m/n`.

Prove that for every positive A there exists exactly one positive matrix S with these margins and `S_ij=alpha_i*A_ij*beta_j` for positive real vectors alpha,beta. Define `Sink(A)` from this proved existence/uniqueness, and set `x=Sink(A)_(first,first)`. This uses the canonical statement's explicit equivalent definition. An unexplained assumed scaling, an oracle predicate, or only a conditional implication is insufficient.

Let D be the finite type of pairs `(R,C)` of row/column subsets avoiding the distinguished indices, with `card R=card C`. Every minor is indexed in increasing order; empty determinants and products are 1. Define

```
Delta_A(R,C) = det A_({first} union R),({first} union C)
Gamma_A(R,C) = A_(first,first) * det A_(R,C).
```

The global integer matrix H indexed by D has exactly the canonical diagonal and four off-diagonal cases. With `pos_s(U)` the position starting at 1, for distinct D_i=(R_i,C_i), D_j=(R_j,C_j):

| Case of differences `(Ri\Rj,Rj\Ri,Ci\Cj,Cj\Ci)` | Entry |
|---|---|
| `(empty,{s},empty,{t})` | `(-1)^(pos_s(Rj)+pos_t(Cj))*m` |
| `({s},empty,{t},empty)` | `(-1)^(pos_s(Ri)+pos_t(Ci)+1)*n` |
| `(empty,empty,{s},{t})` | `(-1)^(pos_s(Ci)+pos_t(Cj))*m` |
| `({s},{t},empty,empty)` | `(-1)^(pos_s(Ri)+pos_t(Rj))*n` |
| otherwise | `0` |

Its diagonal is `card(Ri)*(m+n)-m*n`. Signs and cardinalities must be computed in the stated integer/real types, not natural subtraction that truncates a negative integer. All principal restrictions H_S are actual submatrices; simultaneous reindexing proves independence from the ordering of S.

The exact final assertion is

```
forall m,n>=1, forall entrywise-positive real m-by-n A,
 sum_(S subset D) det((1/m) * H_S)
   * product_(Dmember in S) Delta_A(Dmember)
   * product_(Dmember in D\S) Gamma_A(Dmember)
   * Sink(A)_(first,first)^card(S) = 0.
```

No nonzero-minor assumption is permitted. In particular, uniform rank-one positive matrices and m=1 or n=1 must be covered by the definitions and proofs.

### NM-04 proof obligations in order

1. **Fixed scalar certificate used by the analytic bridge:** certify `0<(1/2:R)` and `(1/2:R)<=1` in kernel LeanCert. Consume it in the convenient coercivity constant `m/(2*n)`. There are no arbitrary-size interval boxes or determinant-enumeration certificates.
2. **Actual scaling existence:** let `a0=min_ij Aij>0`, `E={b in R^n : sum b=0}`, `Z_i(b)=sum_j Aij*exp(bj)>0`, and
   `F(b)=sum_i log Z_i(b) - (m/n)*sum_j b_j`.
   Prove continuity and, for b in E, writing `q=max_j b_j`, `q>=0`, `norm_inf(b)<=n*q`, and
   `F(b)>=m*q+m*log a0 >= (m/(2*n))*norm_inf(b)+m*log a0`.
   The first bound follows from `Z_i>=a0*exp(q)`; the half certificate justifies the last weakening. The compact-box radius
   `R=(2*n/m)*(1+abs(F(0)-m*log a0))`
   puts F strictly above F(0) outside the box within E. Minimize on its intersection with the closed hyperplane and infer a global minimizer b* on E.
   Differentiate the actual function along every line `b*+t*(e_j-e_first)` at t=0. Its derivative is `g_j-g_first`, where
   `g_j=sum_i Aij*exp(b*_j)/Z_i(b*)-m/n`.
   All differences vanish; `sum g_j=0` gives every g_j=0, including n=1. Set `beta_j=exp(b*_j)` and `alpha_i=1/Z_i(b*)`. Positivity, row sums and column sums follow. There is no assumption of minimizer existence or of the derivative formula.
3. **Actual scaling uniqueness:** for two positive balanced matrices in the same positive diagonal orbit, write `T_ij=u_i*S_ij*v_j`. If `vmax=max_j v_j`, the row sums imply `u_i>=1/vmax`. The column attaining vmax has the same positive margin in S and T; equality in the finite sum, with every S entry positive, forces all `u_i=1/vmax`. A row sum then forces all `v_j=vmax`, hence T=S. No numerical condition-number or generic-position assumption is needed.
4. **Weighted principal-minor expansion:** for any finite D and arbitrary real diagonal vectors gamma,delta, prove
   `det(diag gamma+(x/m)*H*diag delta)` equals the canonical coefficient sum.
   Use determinant multilinearity in columns/rows and the principal-submatrix identity. No division by gamma or delta is allowed; they can vanish. Reindex H_S and the sorted original minors explicitly.
5. **Universal cofactor algebra, including singular submatrices:** for any rectangular T and equal-size R,C, let `f_RC(T)=det(T_RC)`. Define the directional cofactor form
   `Df_RC[E]=sum_(a in R,b in C) (-1)^(pos_a(R)+pos_b(C))*E_ab*f_(R-a,C-b)(T)`.
   Prove the rank-one identity `f_RC(T+t*u*v^T)=f_RC(T)+t*Df_RC[u*v^T]` using alternation and multilinearity: terms with two replaced columns vanish because those columns are proportional. This avoids the invertibility assumption in the pinned determinant lemma.
6. **Four signed minor identities:** define L as the signed deletion sum, U as the signed one-row/one-column insertion sum, C0 as the signed column-replacement sum and R0 as the signed row-replacement sum, with exactly the positional signs induced by H. Prove, for k=card R,
   `Df[J]=L f`,
   `Df[(T*1)*1^T]=k*f+C0*f`,
   `Df[1*(1^T*T)]=k*f+R0*f`,
   `Df[(T*1)*(1^T*T)]=s(T)*f-U*f`,
   where J is the all-ones rectangular matrix and s(T) is the sum of every entry. The last identity is a bordered-minor expansion. Internal replacements give the k copies of f; duplicate rows/columns give zero. Empty and maximal-size cases use empty sums and determinants, not additional assumptions.
7. **Balanced Schur complement:** write a positive balanced matrix as `[[x,r^T],[c,B]]`, `rho=m/n`, `T=B-c*r^T/x`. Prove `Delta=x*f(T)`, `T*1=1-c/x`, `1^T*T=rho*(1^T-r^T/x)`, and `s(T)=m-rho/x`. Put `u=1-T*1`, `v^T=1^T-rho^(-1)*1^T*T`, so `B=T+x*u*v^T`. With `b_RC=det B_RC`, cofactor algebra gives the exact row relation
   `m*b + (k*(m+n)-m*n)*Delta + n*U Delta - m*L Delta + m*C0 Delta + n*R0 Delta = 0`.
   All scalar divisions have positivity hypotheses supplied by m,n,x; no minor is inverted.
8. **Explicit null vector:** for `K(A,x)=diag Gamma+(x/m)*H*diag Delta`, let `w_RC=(n/m)^card(R)`. The insertion/deletion weights change m,n to exactly the coefficients in item 7; same-size replacements retain them. Prove `K(Sink(A),x)*w=0` and `w_empty=1`, then infer its determinant vanishes without any determinant expansion.
9. **Scaling covariance and final transport:** if S=diag alpha*A*diag beta, prove both Delta and Gamma at `(R,C)` are multiplied by the same positive scalar `c_RC=alpha_first*beta_first*product_R alpha*product_C beta`. Therefore `K(S,x)=K(A,x)*diag c`. The vector `diag c*w` is nonzero, so `det K(A,x)=0`; combine item 4 and proved Sink semantics for the exact original identity.

Only manuscript Sections 1–4 are needed for the original coefficient formula. Its generalized-margin, characteristic-polynomial and algebraic-degree extensions are outside this target and are not proposed as extra completed problems.

`NM04-exact-diagnostic.py` performs rational elimination and direct multiplication for seven specified balanced matrices, with index counts 1, 3 or 6. The rank-one 3-by-3 case has five zero Delta minors and one zero Gamma minor. All residuals and determinants are zero. This validates conventions at those points only; the general Lean proof must establish items 1–9 for arbitrary dimensions.
