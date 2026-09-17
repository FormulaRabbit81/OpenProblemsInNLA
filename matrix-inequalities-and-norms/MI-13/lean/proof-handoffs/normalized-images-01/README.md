# MI-13 normalized singular images: source-author handoff

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Substantial OpenAI Codex assistance. Nobori's original question, Audenaert's refined commutator theorem, and the repository reduction retain their attribution. No email is included.

## Delivered scope

`NLA/MI13/NormalizedImages.lean` supplies proof source for the exact frozen contracts `positive_image_orthonormal`, `zero_singular_image`, and `full_singular_vector_bases`, with one private Gram-inner-product helper. It imports `GramBasis`, which imports `SingularSemantics`, and never imports `Challenge`. All three headers were compared byte-for-byte with the immutable Challenge declarations. All 13 frozen inputs were rehashed unchanged. Only this new module and this private handoff were written for this assignment.

The source-author packet is explicitly **unrun**: no Lean, Lake, cache, or compiler command was executed by this agent. Root owns actual serial local testing at one compiler process, one thread, and 4096 MiB. Each export has an axiom report and explicit kernel trust assertion, but their existence in the source is not a claim that they have run. Root must record actual logs against the sealed source hash. No complete MI-13, final Linux Comparator/kernel/sandbox, publication, or count claim is made.

The imported GramBasis source is bound to the actual successful root `development-25` receipt and log copied under `evidence/`. Its exact source SHA-256 is `3a3b6e77d4081f20fb9e7df79ce1ae36a0414851f8a81a18186959ecb759f1f9`; the log reports only `propext`, `Classical.choice`, and `Quot.sound` for both GramBasis exports. That successful dependency run does not test this new module.

## Proof and edge cases

The private helper uses the adjoint identity and the frozen Gram equation to derive `<T v_i,T v_j> = s_j^2 <v_i,v_j>`, in Mathlib's convention of conjugate linearity in the first argument. The positive-index proof uses the exact complex Kronecker-delta characterization of orthonormality. The diagonal case fixes the real scalar under conjugation and cancels its inverse using its explicit nonzero proof. Off the diagonal, the original basis inner product is zero. The calculations use rewriting and scalar cancellation; no interval computation, field normalization, matrix enumeration, or spectral approximation is used.

The zero-image proof applies positive definiteness to the same inner product identity with s_i=0. The final contract selects the actual ordered Gram basis, extends only the positive normalized images to a full orthonormal basis, and verifies the singular-vector equation separately on positive and zero indices. Nonnegativity of the actual singular values proves that a nonpositive value is zero.

Repeated singular values do not affect orthogonality of the original full basis. Zero singular values are never inverted in a cancellation argument. Rank zero and all deficient ranks are included. At dimension zero every pointwise index obligation is vacuous, and both pre-existing basis-existence contracts are stated at every natural dimension. There is no nonempty-dimension, full-rank, distinct-value, or real-entry assumption.

## Pinned primary API evidence

Nine selected Mathlib sources were fetched at the literal pin `0df444a360eaa60ab8c11dca51a86af692955474` and byte-compared with the shared read-only sources. Exact URLs, hashes, copied source files, and inspected line ranges are in `PRIMARY-BINDINGS.json`. This is selected-source verification, not a transitive proof audit.

- `LinearMap.adjoint_inner_right`, `Analysis/InnerProductSpace/Adjoint.lean:588`, moves T across the inner product.
- `inner_smul_left` and `inner_smul_right`, `Analysis/InnerProductSpace/Defs.lean:249,252`, expose the conjugate-linear/linear scalar factors.
- `orthonormal_iff_ite`, `Analysis/InnerProductSpace/Orthonormal.lean:80`, supplies the exact complex inner-product test.
- `OrthonormalBasis.inner_eq_one` and `inner_eq_zero`, `Analysis/InnerProductSpace/PiL2.lean:472,469`, supply diagonal and off-diagonal basis products.
- `Complex.ofReal_ne_zero`, `conj_ofReal`, and `conj_inv`, `Data/Complex/Basic.lean:141,475,729`, justify real-scalar normalization.
- `inv_mul_cancel_left₀`, `Algebra/GroupWithZero/Basic.lean:366`, and `smul_inv_smul₀`, `Algebra/GroupWithZero/Action/Units.lean:63`, cancel only explicitly nonzero scalars.
- `inner_self_eq_zero`, `Analysis/InnerProductSpace/Basic.lean:314`, proves the zero-image case.
- `Set.domRestrict`, `Data/Set/Restrict.lean:32`, is the actual subtype-indexed family from the frozen contract.

`00-PROOF-PLAN.md` was written before the new Lean source and preserves the numerical-first scope. `EXACT-HEADERS.json`, `STATIC-CHECKS.json`, and `INPUT-BINDINGS.json` record source-level checks and dependency boundaries. `MANIFEST.json` seals the entire packet. Remaining contracts, including matrix SVD, unitary invariance, commutator estimates, averaging, padding, and the original rectangular bound, are outside this bounded module.
