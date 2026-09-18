# Exact obligations before new Lean code

Status: concrete Definitions and 14 independent Challenge statements now drafted from the sealed precode. No MF-05 proof, certificate, source-review approval, elaboration or freeze is claimed. The two future nonauthor statement reviews must cover the exact source bytes, these obligations and the original canonical source correspondence. The original numerical-first plan is retained under sources/precode/.

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



## Concrete statement mapping

`CONTRACT-MAP.json` records all 14 exact draft headers. The final `canonical_local_holder` uses `canonicalHausdorff`, the literal original max-of-sup-inf formula; `spectral_hausdorff_semantics` proves its identity with the operator-image Hausdorff metric used by the intermediate estimates. `scalar_identity_adjoin_radius` additionally records the exact family-norm maximum needed to keep the enlarged family in the L-ball. `uniform_holder_estimate` also concludes positivity of its displayed constant. These strengthen the intermediate statement package without narrowing the original quantifiers.
