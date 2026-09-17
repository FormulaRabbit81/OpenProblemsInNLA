# MI-13 Frobenius foundations: pre-code plan

Author agent `/root/ie02_foundation_preflight`; 17 September 2026. George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, is credited for formalization, with prior Nobori, Audenaert, repository, and library attribution retained.

The exact 13-file freeze has SHA-256 `bddc9d048f92e28dd8912f9bfb8293e12f07f2458fe7fb5a77e5b3c57e16e732`; every frozen file was rehashed and matched before this plan. The root acceptance is at `/tmp/nla-lean-next-20260915/MI13-ROOT-FREEZE-ACCEPTANCE.json`, SHA-256 `d6fce365ba5c4e19345a40b77fba85325ea8bb0ef19409b543647fe4364bfcab`, and explicitly authorizes new proof modules. The assigned output and handoff directories did not previously exist.

Read the frozen definitions, exact Challenge headers, source correspondence, numerical boundary, and relevant contract/review plan before implementation. The owned module is only `NLA/MI13/Frobenius.lean`. Do not change the frozen inputs, Numerical.lean, SingularSemantics.lean, pins, resource limits, or any other proof source.

Prove the unchanged contracts `frobenius_semantics` and `frobenius_linear_bounds`, plus the bounded optional `hilbert_schmidt_semantics`:

1. Prove flattening injectivity and zero/add/scalar identities by coefficient evaluation in the actual `EuclideanSpace C (Fin m × Fin n)`, including empty index types.
2. Apply `EuclideanSpace.norm_sq_eq` and `Fintype.sum_prod_type` for the full entry sum.
3. Expand the actual complex Euclidean inner product and Gram trace; commute the two finite sums to prove the rectangular trace identity.
4. Obtain the Frobenius trace identity from the inner-self/norm-square identity. Obtain norm positivity, zero detection, complex scaling, and triangle inequality from the actual entry-space norm.
5. Expand the supplied pair-index commutator coefficient matrix. Distribute its difference and collapse each Kronecker-delta sum to prove it acts as the actual matrix commutator. This is a genuine action proof, not a definition change.

All arguments are symbolic and finite; no new numerical certificate, sampling, native evaluation, axiom, assumption of the trace identity, or matrix supremum norm is involved. The original exact-half LeanCert consumer belongs to a later averaging proof and remains root-owned.

No Lean, Lake, cache, or other compiler command may be run by this author. The source will be sealed with exact headers and primary API evidence for root's one-process, one-thread, 4096 MiB local compiler. Static source checks are not compilation or final Comparator/kernel/sandbox validation. No wider MI-13 completion claim is permitted.
