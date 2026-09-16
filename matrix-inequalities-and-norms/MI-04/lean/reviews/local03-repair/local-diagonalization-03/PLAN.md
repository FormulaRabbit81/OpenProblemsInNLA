# MI-04 local declaration-timeout diagnosis and proposed statements

Author: `/root/mi04_independent_referee`. Recorded before any new mathematical
proof implementation. The parent owns the sole compiler process. This plan
permits no heartbeat increase, changed contract, extra final hypothesis or
new trust mode. No mathematical source is changed by the diagnostic probe.

The current source is `Diagonalization.lean` with SHA-256
`41b1a60f3a6f4c3aa9b1c09472dd52a61e824999ba3e4540c0c50173d54e06f4`,
in the reviewed full closure
`c8bbc2dd6c9c5097619e8927f1f70d0c16a0fd74c391822639705eb4a17df204`.
The actual local development-02 log reports a deterministic `whnf` timeout at
the start of `normal_operator_eigenbasis`, line 59, at 200000 heartbeats. The
new `normal_operator_parts` helper is not an error site; its two local-instance
style warnings precede the failed declaration. The later unknown constant and
trust rejection are cascading failures, not accepted evidence. The full run
is still in progress, so its evolving receipt is not a sealed final run result.

First request: have root compile an isolated copy with only
`set_option diagnostics true in` immediately before the existing
`normal_operator_eigenbasis` declaration. Keep all theorem resources and proof
bodies unchanged. Retain the full diagnostic output, input hash and actual
command. This can distinguish coercion/instance unfolding from the last
reconstruction proof before choosing further opaque boundaries.

There are no new numerical statements or interval computations. If factoring
is justified, the following generic helper types preserve the actual operator
and scalar meanings. Existing public/helper headers stay exactly unchanged.

```lean
private lemma commute_continuous_to_linear {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B : E →L[ℂ] E) (hAB : Commute A B) :
    Commute (A : Module.End ℂ E) (B : Module.End ℂ E)

private lemma eigenbasis_reconstruct_parts {E : Type*} {ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]
    (T A B : E →L[ℂ] E) (hparts : T = A + Complex.I • B)
    (b : OrthonormalBasis ι ℂ E) (α β : ι → ℂ)
    (hb : ∀ i, A (b i) = α i • b i ∧ B (b i) = β i • b i) :
    ∀ i, T (b i) = (α i + Complex.I * β i) • b i
```

The first is the existing coercion-of-commutation proof with abstract E. The
second is the existing application/reconstruction proof with all supplied
operators, basis and eigenvalues abstract. Neither assumes diagonalizability
or the final matrix conclusion. They may be used separately if diagnostics
identify a smaller repair.

A further generic assembly boundary is available if specializing the joint
basis and decomposition together is the expensive step:

```lean
private lemma normal_eigenbasis_of_joint_solver {E : Type*} {ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Fintype ι]
    (hjoint : ∀ A B : Module.End ℂ E,
      A.IsSymmetric → B.IsSymmetric → Commute A B →
      ∃ b : OrthonormalBasis ι ℂ E, ∃ α β : ι → ℂ,
        ∀ i, A (b i) = α i • b i ∧ B (b i) = β i • b i)
    (T : E →L[ℂ] E) (hT : IsStarNormal T) :
    ∃ b : OrthonormalBasis ι ℂ E, ∃ z : ι → ℂ,
      ∀ i, T (b i) = z i • b i
```

This conditional helper must consume the existing proved
`commuting_symmetric_eigenbasis` when specialized to `CVector (Fin n)`.
It must not become an additional premise of the existing
`normal_operator_eigenbasis` or any frozen export. The original theorem's
body would apply it with that already proved solver and no new assumption.
All zero-dimensional, repeated-eigenvalue and singular cases remain included.

These are candidate statements, not proved or compiled additions. Choose the
smallest useful factoring after root's diagnostic run where possible. Preserve
the final `normal_unitary_diagonalization` statement/body and all other twenty
source files. Any resulting source patch requires separate nonauthor review
and actual compilation; no performance or whole-problem claim is made here.
