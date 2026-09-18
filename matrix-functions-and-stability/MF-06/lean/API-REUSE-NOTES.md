# Pinned API and computation choices

The inspected Mathlib revision is `0df444a360eaa60ab8c11dca51a86af692955474`.
All referenced source files are copied inertly under `source-inputs/mathlib`.
The source-tree diff check is read-only and records whether those bytes match
that pinned checkout. No API name below was tested by invoking Lean.

| Definition or proof interface | Actual pinned source location | Choice |
|---|---|---|
| Genuine complex seminorm | `Mathlib/Analysis/Seminorm.lean:52`, `Seminorm`; constructor `Seminorm.of` at line76 | C06 constructs the existing structure equal pointwise to the literal limit. A provisional duplicate predicate was removed before review; its original statement-only checkpoint is retained. |
| Finite coordinate reindexing | `Data/Fintype/EquivFin.lean:80`, `Fintype.equivFin` | Concrete finite fibers and actual exterior/allocation indices; no new equivalence proof fields. |
| Exterior basis indices | `Data/Set/PowersetCard.lean:213`, Fintype instance; `Order/Hom/PowersetCard.lean:38`, `ofFinEmbEquiv` | Actual sorted k-subsets and order embeddings, including degree zero. |
| Exterior basis | `LinearAlgebra/ExteriorPower/Basis.lean:97`, `Module.Basis.exteriorPower`; coordinate theorem at line125 | C18 ties explicit minors to the standard algebraic exterior basis. |
| Exterior functor | `LinearAlgebra/ExteriorPower/Basic.lean:260`, `exteriorPower.map`; identity/composition at lines293/298 | Use the existing algebraic map and functoriality rather than reconstructing exterior algebra. |
| Standard coordinate matrix action | `LinearAlgebra/Matrix/ToLin.lean:386`, `Matrix.toLin'`; `LinearAlgebra/StdBasis.lean:122`, `Pi.basisFun` | Pure coordinate correspondence on `Fin d → ℂ`; compatible with the unchanged Euclidean operator norm through its actual matrix entries. |
| Paired tensor matrix | `LinearAlgebra/Matrix/Kronecker.lean:274`, `Matrix.kronecker`; multiplication theorem at line382 | Reindex the existing Kronecker matrix into the shared `Square` interface. Do not duplicate its raw entry definition/proofs. |
| Product finite index | `Logic/Equiv/Fin/Basic.lean:334`, `finProdFinEquiv` | Reindex actual product coordinates, preserving their order. |
| Compact decreasing-tail convergence | `Topology/UniformSpace/Dini.lean`, `Antitone.tendstoUniformlyOn_of_forall_tendsto` | Existing compact uniform-convergence machinery is a proof resource, not an assumed final conclusion. |
| Actual word envelope/norm | Pinned `NLA/MF07/ProductEnvelope.lean` | Use the original word supremum and existing norm/generator lemmas. |
| Root limit, scaling and Hausdorff | Pinned MF05 `RootLimit`, `Scaling`, `Hausdorff` | Four selected exact headers are reproduced in Challenge; implementations will be imported directly without forwarding wrappers. |
| Kernel numerical certificate | Pinned `NLA/MF05/Numerical.lean:22` | Reuse `half_radius_certificate`, already using `interval_decide (trust := kernel)`. Its planned MF06 cone/transfer consumption is not yet a verified fact. |

The earlier complete namespace searches and their limits are retained in the
sealed pre-code audit. No existing pinned compound-matrix or arbitrary compact
joint-radius/Barabanov theorem was located. The ordinary Perron–Frobenius
`Matrix.IsIrreducible` concerns entrywise nonnegative matrices and is not the
required irreducibility of a complex matrix family. `FamilyInvariant` and
`FamilyIrreducible` therefore state the literal common-submodule conditions;
their nontrivial consumers are C08, C14 and C15.

The full source route needs substantial new proofs. Compactness, quotient
stability, invariant flags, product-bounded irreducibility, finite-block radius
formulas and exterior allocation triangularization cannot be imported by name
from a cited paper or assumed in a replacement structure. Existing algebraic
and topological library tools are intended ingredients, not completion claims.

All numeric dimension and word parameters remain symbolic. Enlarging fixed
internal constants avoids exact complex Hilbert tensor norm identities; those
constants disappear under word-length roots. Sorted-minor expansion and
finite-factor telescoping avoid interval grids, SVDs and brute-force searches.
