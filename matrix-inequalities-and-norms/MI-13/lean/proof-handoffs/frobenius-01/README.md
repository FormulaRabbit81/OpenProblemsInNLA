# Frobenius source candidate 01

The owned module `NLA/MI13/Frobenius.lean` supplies source proofs of the three unchanged frozen contracts:

* `NLA.MI13.frobenius_semantics`
* `NLA.MI13.frobenius_linear_bounds`
* `NLA.MI13.hilbert_schmidt_semantics`

The first two were mandatory; the third was the bounded optional assignment and is included. All support lemmas live in the same module. No other proof file, frozen definition, contract, dependency pin, resource setting, canonical file, or publication state was edited.

**Compilation is unrun by this author.** The source has no proof holes, axioms, native evaluation, unsafe declaration, or Challenge import. Static checks confirmed the exact three frozen headers and all 13 unchanged frozen file hashes. These checks do not establish elaboration or kernel acceptance. Root owns the actual one-process, one-thread, 4096 MiB local compiler and the later real Linux Comparator/kernel/sandbox checks.

## Proof content

`flatten_injective`, `flatten_zero`, `flatten_add`, and `flatten_smul` follow from entry evaluation in the genuine `EuclideanSpace C (Fin m × Fin n)`. `frobenius_norm_sq_eq_entries` applies `EuclideanSpace.norm_sq_eq` and splits the finite product-index sum. `flatten_inner_eq_trace` expands the complex inner product and actual Gram matrix trace, then interchanges the two finite sums.

The semantic contract combines those identities with the inner-self norm identity and positivity/zero detection of the actual entry-space norm. Scaling and the triangle inequality are ordinary norm laws on that same space. No matrix norm instance is installed or used.

`commutatorOperator_flatten` expands the supplied coefficient operator, distributes the two terms, and collapses the two conditional finite sums. It proves the actual action required by the optional contract. The latter also consumes the rectangular trace identity and flattening linearity.

Every helper and contract remains valid at empty dimensions: there is no `Nonempty (Fin ...)` assumption, no chosen coordinate, and no division. The finite sum and norm theorems already cover the zero-dimensional entry space.

## Primary API evidence

`SOURCE-BINDINGS.json` records the literal Mathlib pin, exact source hashes, byte-matched remote/local copies, and read ranges. Full primary source copies retain their original headers under `primary/`.

| Interface | Exact primary declaration |
|---|---|
| Euclidean squared norm | `EuclideanSpace.norm_sq_eq` in `Analysis/InnerProductSpace/PiL2.lean:151` |
| Complex entry inner product | `PiLp.inner_apply` in the same file at line 103; `RCLike.inner_apply'` in `Analysis/InnerProductSpace/Basic.lean:915` |
| Inner-self norm identity | `InnerProductSpace.norm_sq_eq_re_inner`, exported in `Analysis/InnerProductSpace/Basic.lean:53`, declared in `Defs.lean:110` |
| Flattening coordinate/extensionality | `PiLp.ext`, `PiLp.toLp_apply` in `Analysis/Normed/Lp/PiLp.lean:97,139` |
| WithLp zero/add/scalar transport | `WithLp.toLp_zero`, `toLp_add`, `toLp_smul` in `Analysis/Normed/Lp/WithLp.lean:161,164,178` |
| Actual Euclidean matrix action | `Matrix.toLpLin_apply` in `Analysis/Normed/Lp/Matrix.lean:44`, a definitional identity; `Matrix.toEuclideanLin` is the `2,2` abbreviation |
| Gram trace expansion | `Matrix.trace`, `diag_apply`, `mul_apply`, `conjTranspose_apply` in the corresponding copied primary files |
| Product-index sums and interchange | `Fintype.sum_prod_type` generated at `Data/Fintype/BigOperators.lean:271`; `Finset.sum_comm` generated at `Algebra/BigOperators/Group/Finset/Sigma.lean:120` |
| Conditional sums in the action proof | `Finset.sum_ite_eq`, `sum_ite_eq'`, generated as simp lemmas in `Algebra/BigOperators/Group/Finset/Piecewise.lean:140–154` |

The public `#print axioms` and `#assert_trust kernel` commands follow the root-owned module pattern, but have not been executed by this author. The source imports `LeanCert.Tactic` for those checks; it performs no new numerical certificate. The exact-half certificate and its averaging consumer remain separate obligations.

## Compiler handoff and scope limits

Compile the sealed source in the root-managed development environment using the existing pinned Definitions output. The most elaboration-sensitive step is the `change` in `commutatorOperator_flatten`, which unfolds the finite-dimensional CLM conversion to its definitionally equal pair-index sum. The pinned `Matrix.toLpLin_apply` and `PiLp.toLp_apply` support that reduction. If the compiler requires an explicit action rewrite, report the exact diagnostic and source hash; no contract or definition adjustment is authorized.

No paper-level or API gap was intentionally left as a proof placeholder. The candidate still requires actual local compilation, source review, and final Comparator acceptance. It proves no SVD, unitary invariance, commutator bound, padding norm, canonical rectangular inequality, or complete MI-13 target. Those remain outside this bounded handoff.

Authored with substantial OpenAI Codex assistance for George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Nobori's original question, Audenaert's refined commutator result, the repository reduction, and library authorship retain their attribution. No contact email is included.
