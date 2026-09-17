# IE-02 reciprocal roots — exact source-based plan, not implementation

Prepared by `/root/sf_ra_runtime_referee` for `/root`, 17 September 2026. This packet proposes an implementation route for frozen contracts **25** `reciprocal_root_pairing` and **26** `reciprocal_inside_factor`. Fourier semantics is contract 23 and effective polynomial construction is 24. The two exact headers, including every hypothesis and conclusion, are retained in `EXACT-CONTRACTS.json`.

Status: **PLAN ONLY; root acceptance required before implementation.** No Lean proof or test file was written, no compiler was invoked or cache modified, and no elaboration, axiom, runtime or Comparator success is asserted for this plan. The pinned APIs below were located and read in source. Any displayed prospective helper statement is a proposal, not an established declaration. This does not alter the accepted frozen definitions, contract statements, original target, numerical plan, pins or metadata.

## Numerical and semantic boundary

Both contracts are fully symbolic. Use the proved complex fundamental theorem of algebra already available through the frozen imports, exact polynomial products, exact multiset multiplicities, conjugation, inversion and real order on norms. There is no new interval, numerical root computation, grid, simple-root assumption, approximate factorization or certificate. The existing full-target positive-half LeanCert obligation belongs to descent; it is not needed here. Preserve kernel trust in future proof modules, root-only serial local compilation with one thread and 4096 MiB, later independent proof reviews, and eventual whole-target GitHub Linux acceptance.

Frozen meanings are literal: `reciprocalConj z = (star z)⁻¹`; `insideRoots P` filters the complete multiset `P.roots` by `‖z‖ < 1`; `rootProduct s = (s.map (fun z => X - C z)).prod`; `conjReflect d p` is `Polynomial.reflect d (p.map (starRingEnd ℂ))`. Preserve these definitions. The contract hypotheses include exact degree `2*ell`, a nonzero constant coefficient, self-conjugate reflection at that exact degree, and no unit-circle roots. They do not assume that roots are simple or that the polynomial has positive circle values.

The original scalar-factorization paper route is retained in the bound preflight, section 5. Its product-factorization argument proves equality of **multisets**, then separates inside and outside roots. It does not justify replacing roots by a set. The original IE-02 target and attribution remain unchanged: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology; Codex assistance; prior mathematical and library authorship retained; no email.

## Reuse before new proof work

The following already exist at the pinned Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. Full source hashes, line excerpts and searches are in this packet. These names and signatures were read, but no prospective application was compiled.

| Need | Located API and exact relevance |
|---|---|
| Splitting over ℂ | `Complex.isAlgClosed` in `Analysis/Complex/Polynomial/Basic.lean:52`, with `IsAlgClosed.splits P` in `FieldTheory/IsAlgClosed/Basic.lean:63`. This is established library mathematics, not a new hypothesis. |
| Complete factorization | `(IsAlgClosed.splits P).eq_prod_roots`, `Algebra/Polynomial/Splits.lean:299`: `P = C P.leadingCoeff * (P.roots.map (X - C ·)).prod`. |
| Root cardinality | `Splits.natDegree_eq_card_roots` at line 362; `degree_eq_iff_natDegree_eq` at `Degree/Defs.lean:99` converts the exact degree using `P ≠ 0`, including `ell=0`. |
| Nonzero leading coefficient | `Polynomial.leadingCoeff_ne_zero` at `Degree/Defs.lean:360`. Obtain `P ≠ 0` directly from the nonzero constant coefficient; a short contradiction after substituting zero needs no new wrapper. |
| Roots of the exact frozen product | `Polynomial.roots_multiset_prod_X_sub_C`, `Roots.lean:308`, has exactly the required mapped product and returns the complete multiset. Do not reprove roots of products by induction. |
| Monicity and exact degree of that product | `monic_multisetProd_X_sub_C`, `Roots.lean:781`; `natDegree_multiset_prod_X_sub_C_eq_card`, `BigOperators.lean:329`; `degree_eq_natDegree`. These also cover the empty product. |
| Constant scaling preserves roots | `Polynomial.roots_C_mul`, `Roots.lean:212`, requires a nonzero complex scalar. |
| Root/evaluation bridge | `Polynomial.mem_roots` and `isRoot_of_mem_roots`, `Roots.lean:110–117`, with the actual polynomial nonzero proof. |
| Fixed-degree product reflection | Existing project `reflection_product`, `Reflection.lean`, reuses `Polynomial.reflect_mul` at `Reverse.lean:177`. Use actual degree bounds for each factor. |
| Single linear factor and scalar reflection | `Polynomial.map_sub`, `map_X`, `map_C`, `reflect_sub`, `reflect_one_X`, `reflect_C`, `reflect_C_mul`, and `starRingEnd_apply`. No new coefficientwise reflection proof is needed. |
| Product rearrangement | `Multiset.map_add`, `map_map`, `prod_add`, `prod_map_mul`, `prod_hom`/`prod_hom'`, and `Multiset.prod_ne_zero`. Use these rather than new product-distribution inductions. |
| Complement partition | `Multiset.filter_add_not`, `filter_map`, and the membership-restricted `filter_congr`, in `Data/Multiset/Filter.lean:53,148,154`. These preserve each repeated occurrence. |
| Reciprocal norm | `norm_inv`, `norm_star`, `norm_pos_iff`, and `inv_lt_one₀`/`one_lt_inv₀` with the strictly positive norm of a nonzero root. |

`Polynomial.ofMultiset` at `Algebra/Polynomial/Basic.lean:1217` is an existing `AddChar` whose function is precisely the frozen mapped product. Preserve the frozen `rootProduct` definition, but use the direct product/roots/degree APIs above after unfolding it. Do not add a new compatibility alias or change frozen Definitions to rename this object.

`Splits.roots_map` at `Splits.lean:544` applies to a **ring homomorphism**, such as `starRingEnd ℂ`. It cannot be applied to `reciprocalConj`, which is not additive. It may serve a separate conjugation-only argument, but it does not remove the inversion/reflection step. I found no direct reciprocal-root, roots-of-reverse, or reflected-multiset-product replacement in the searched pinned polynomial sources. The supplied TauCeti corpus is review guidance, not a mathematical TauCeti checkout; no exhaustive external duplicate search is claimed.

## One substantive new bridge, reused twice

For a multiset `s : Multiset ℂ` with `hs : ∀ z ∈ s, z ≠ 0`, write

`D(s) = (s.map (fun z => -star z)).prod`.

This is notation in the plan and can remain a local expression in proofs, without adding a frozen definition. Propose one consumed helper of the following mathematical shape:

`conjReflect s.card (rootProduct s) = C (D(s)) * rootProduct (s.map reciprocalConj)`.

The nonzero-root condition is necessary: a factor `X` reflects to `1`, whereas the proposed scalar has a zero factor. Do not omit it. Also establish `D(s) ≠ 0` from `Multiset.prod_ne_zero`, membership in a map, `neg_ne_zero` and `star_ne_zero`; this is direct library plumbing and need not become a redundant public wrapper.

A feasible proof is induction on `s` **only for this reflection bridge**. The empty multiset has card zero, product one, `D=1`, and `conjReflect 0 1=1`. In the cons step, the existing product-reflection theorem applies with degree bounds `1` and `s.card`. Obtain the first bound from `degree_X_sub_C_le` and the second from the existing monic/product-degree APIs. Reconcile `card_cons` with `1+s.card` by named natural arithmetic; do not silently replace the reflection bound by the degree of a possibly vanishing factor.

For `z ≠ 0`, the linear factor calculation is

`conjReflect 1 (X - C z) = 1 - C (star z) * X`

`= C (-star z) * (X - C ((star z)⁻¹))`.

The first equality uses the named map/reflect rules. The second uses `star_ne_zero` and inverse cancellation in ℂ, followed by polynomial ring algebra and `C_mul`. Combine this with the induction hypothesis using `Multiset.map_cons`, `prod_cons` and ordinary commutative multiplication. This is a genuine new fixed-degree identity with two consumers: the full root multiset and the inside root multiset. Keep it separate from the frozen public contracts so both can reuse the same proof.

## Contract 25: exact pairing and inside cardinality

Let `S = P.roots` and `L = P.leadingCoeff`. From `hzero`, derive `P ≠ 0`, hence `L ≠ 0`. If `z ∈ S`, `isRoot_of_mem_roots` gives `P.eval z=0`; substituting `z=0` contradicts `hzero` through `coeff_zero_eq_eval_zero`. The same root equation and `hcircle` show `‖z‖ ≠ 1`. These consequences are derived, not extra hypotheses.

From the complex splitting instance and `hdeg`, obtain `S.card=2*ell` and `P=C L * rootProduct S`. Apply fixed-bound conjugate reflection to this full polynomial identity. The scalar-reflection API, `S.card=2*ell`, the new bridge, and `href` give

`P = C (star L * D(S)) * rootProduct (S.map reciprocalConj)`.

The scalar is nonzero. Apply `congrArg Polynomial.roots`, `roots_C_mul`, and `roots_multiset_prod_X_sub_C` to deduce `S=S.map reciprocalConj`. This is equality with multiplicity; equality of root membership alone is insufficient.

For the partition put `p(z) := ‖z‖ < 1`, `M := S.filter p` and `O := S.filter (fun z => ¬p(z))`. The library gives `M+O=S`. For every `z ∈ S`, positive `‖z‖`, `‖z‖≠1`, `norm_inv` and `norm_star` imply

`¬ (‖reciprocalConj z‖ < 1) ↔ ‖z‖ < 1`.

Use `inv_lt_one₀` to rewrite reciprocal norm below one as original norm above one; exclude equality to turn its negation into strict below one. This equivalence is only asserted on members of `S`; `filter_congr` has exactly that scope. Rewrite `S` by its multiset pairing in `O`, use `filter_map`, then `filter_congr` with this equivalence to obtain `O=M.map reciprocalConj`. Thus `S=M+M.map reciprocalConj`. Applying `Multiset.card`, `card_add` and `card_map`, and using `S.card=2*ell`, yields `M.card=ell` by exact natural arithmetic.

The elementary involution `(star ((star z)⁻¹))⁻¹=z` follows from `star_inv₀`, `star_star`, and `inv_inv`, even at zero. It is useful context, but the filter proof above does not need a new permutation/involution API or a choice of representatives. This avoids both duplicate generic multiset machinery and any accidental nodup assumption.

## Contract 26: inside factor and the scalar orientation

Consume contract 25 exactly. Put `M=insideRoots P`, `H=rootProduct M`, `G=rootProduct (M.map reciprocalConj)`, `D=D(M)` and `L=P.leadingCoeff`.

The existing monicity and exact product-degree APIs give `H ≠ 0` and `H.degree=(M.card : WithBot ℕ)=(ell : WithBot ℕ)`. The existing roots-of-product API gives `H.roots=M`. If `H.eval 0=0`, root membership would put zero in `M`, contradicting the derived nonzero-root property. If `‖z‖=1` and `H.eval z=0`, membership in the actual filter would give `‖z‖<1`, a contradiction. No additional induction or root-product evaluation theorem is needed for these nonvanishing clauses.

The multiset partition and `Splits.eq_prod_roots`, followed by `Multiset.map_add`/`prod_add`, give `P=C L*(H*G)`. The same new bridge, now on `M` with `M.card=ell`, gives `conjReflect ell H=C D*G`, where `D ≠ 0`. Choose the complex scalar

`κ = L * D⁻¹` (equivalently `L / D`).

Then `κ ≠ 0`, and `C κ * (H * conjReflect ell H) = C L * (H * G) = P` by `C_mul`, associativity/commutativity and cancellation of `D`. Reverse the equality to match the frozen conclusion. There is no need to refactor `H*conjReflect ell H` a second time or separately compare all its root multiplicities.

Do **not** claim that `κ` is positive or even that positivity follows from these hypotheses. At `ell=0`, the constant `P=-1` satisfies both contracts' hypotheses and has `κ=-1`. Positivity belongs to the later strict-factorization contract, which additionally knows a positive sum-of-squares circle value.

## Corner cases and implementation handoff

- For `ell=0`, `S.card=0`, so `S=M=0`, `H=G=1`, `D=1`, and `κ=L≠0`. The exact degree of `H` is zero. No positive-degree/root-existence theorem may be used without a separate hypothesis. The proposed uniform proof already covers this case.
- Repeated roots remain repeated in every `map`, `filter`, `prod` and `card`. Do not use `toFinset`, `Nodup`, squarefreeness, a simple-root theorem, or root selection that forgets multiplicities.
- Only zeros and unit-circle roots are excluded, each by the frozen explicit hypotheses. Arbitrarily close roots and complex phases remain covered; no positive separation estimate is required.
- Use the fixed bounds `S.card=2*ell` and `M.card=ell`. Mathlib reflection keeps coefficients above its bound, so correct bounds cannot be replaced by an informal reversal argument.
- Preserve exact public headers. The implementation should consist of the one genuine shared reflection bridge, local library facts, and the two public contracts. Avoid replacement axioms, fake predicates, new interval certificates, repeated library roots/degree proofs and deprecated aliases.

Root should approve this source plan before any implementation is assigned. Future local checks should first compile the shared bridge, then the two dependent public modules, using the exact pinned source closure; retain every failed attempt and final sources/logs/outputs. Independent proof review must later inspect the actual code, all multiplicity/cast/degree bridges, and actual standard-axiom reports. Nothing in this plan certifies an unrun implementation or accepts another current candidate module.
