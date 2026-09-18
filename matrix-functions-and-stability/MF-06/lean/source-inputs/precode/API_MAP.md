# Pinned API feasibility audit

Toolchain target remains Lean4.33.1; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Comparator, Tau Ceti and formalization-v0.4 source guidance are retained exactly from the previous independently reviewed packet. No dependency version is changed.

The copied primary files and actual search commands/output hashes are in `PRIMARY-AND-STANDARDS.json`. All searches were read-only. A zero-hit name search is a bounded observation, not a theorem that a result is absent from all formal libraries.

| API / source line | What it genuinely supplies | What remains |
|---|---|---|
| `exteriorPower.map`, ExteriorPower/Basic:260; `map_id`:293; `map_comp`:298 | Algebraic exterior functor for commutative rings, hence complex spaces | Coordinate/spectral-norm and block-allocation infrastructure |
| `Module.Basis.exteriorPower`, ExteriorPower/Basis:97 | Concrete exterior basis indexed by k-element subsets | Fixed Fin reindex and index/basis comparison at degrees0/1 |
| `ιMultiDual_apply_ιMulti`, Basis:47; `basis_repr_apply`:125 | Exact determinant coordinate formula | Ordered block-allocation decomposition and its signs |
| `exteriorPower.finrank_eq`, Basis:159 | Binomial dimension | Positive-dimension endpoint facts and representation interfaces |
| Analysis/InnerProductSpace/ExteriorPower:27 and :46 | Existing canonical inner product is **real only**; RCLike generalization explicitly listed as future work | Cannot import a nonexistent complex Hilbert exterior norm theorem |
| `TensorProduct.norm_tmul`, InnerProductSpace/TensorProduct:146 | Norm multiplicativity on pure tensors over RCLike | Operator tensor lower bound / coordinate Kronecker identification if exact norm equality chosen |
| `TensorProduct.mapL`, same:601; `norm_mapL_le`:604 | Actual continuous tensor operator and upper operator-norm bound | Lower bound or fixed norm-equivalence replacement, and repeated finite tensors |
| `Matrix.mul_kronecker_mul`, Matrix/Kronecker:382 | Paired tensor multiplication at each common word step | Spectral norm relation and arbitrary finite block grouping |
| `Antitone.tendstoUniformlyOn_of_forall_tendsto`, UniformSpace/Dini:133 | Uniform convergence on compact sets after continuity and monotonicity are established | Construct g_n/p, prove common Lipschitz bound, continuity and pointwise convergence; do not reprove Dini |
| `jacobson_density`, SimpleModule/Basic:568 and finite module surjectivity:581 | Abstract algebraic density facts | Does not directly give compact irreducible-family product boundedness or an extremal norm |
| Existing MF07 ProductEnvelope and MF05 GeneralEnvelope/RootLimit/Hausdorff/Scaling | Concrete norms, all-radius growth limits, compact Hausdorff semantics, positive scaling | No stable-kernel cone theorem or critical-exterior result |

## Computation/geometry optimization

The recommended exploratory representation is algebraic exterior matrices in the existing exterior basis, equipped with the ordinary Euclidean spectral norm on their coordinates. Avoid building a new global complex inner-product instance on the algebraic exterior type. Fixed dimension-dependent constants in the wordwise norm power bound vanish under nth roots, and any finite local Lipschitz constant suffices. Explicit candidates are N*k! and N*k*k!*L^(k-1), with N=choose(d,k). Entry maxima give two-sided Kronecker/operator norm comparison with factor m*n, so even exact Hilbert tensor operator norm multiplicativity can be avoided. Thus exact Hilbert-exterior operator constants are unnecessary for the canonical theorem. Polynomial minors, matrix norm equivalence, and functoriality provide a plausible smaller route. It still needs a rigorous universal coordinate proof; a finite checker does not certify it.

Similarly, use a rough rational expression for the transition-sum bound instead of the source's square root, and use the elementary inequality u^k<=u on [0,1] instead of a final kth-root calculation. Neither optimization changes the original target or excludes a dimension or endpoint.

## Precise implementation bottleneck

This is not a small extension of the completed MF05/MF07 chain. Two independent substantial foundations remain:

1. **Product-bounded reference theorem:** build the limiting seminorm, prove its invariant kernel is uniformly exponentially stable, construct the quotient norm and complement coordinates, and produce cone trajectories for arbitrary off-flag perturbations. Dini is available; the rest has no located ready declaration.
2. **Critical exterior theorem:** obtain a common irreducible flag and prove the irreducible radius-one product bound without a Barabanov oracle; establish exterior allocation triangularization and paired nonresonance; then prove existence of a product-bounded exterior degree. Pure algebraic exterior maps exist, but the required family/dynamical theorems do not appear in the pinned search scope.

MF05's constructive approximate norm above radius1 does not give an extremal norm at1 by simply taking a limit: one must prove an irreducibility-based uniform normalization/nondegeneracy bound. Assuming that bound would hide a central missing theorem. Likewise, a single determinant/minor counterexample check cannot replace the allocation theorem.

Recommendation: preserve this exact full-scope pre-code packet as a long infrastructure target. Do not freeze a Challenge whose key existence results are assumed as hypotheses. Before committing to a full proof campaign here, choose and independently review the concrete compound-matrix/flag/quotient representation and scope the two foundations into genuine proofs. No new Lean statement file is emitted by this bounded feasibility task.
