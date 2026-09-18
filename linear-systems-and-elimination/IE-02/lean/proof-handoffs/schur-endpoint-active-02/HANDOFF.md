# Schur endpoint/active block repair02

Bounded proof-body repair after actual root local86. Both modules failed;
no source from run86 is accepted. The preserved logs include the resulting
sorryAx/trust failures, which are consequences of the elaboration errors.

Endpoint fixes: discharge the impossible Fin inequality by Nat.not_lt_zero;
prove the first squared term equals the explicitly typed real one before the
sum rewrite; use the actual global _root_.finrank_top. The pinned file closes
namespace Module before declaring this theorem; it is not Module.finrank_top
or Submodule.finrank_top.

Active-block fixes: specify the constant family `fun _ : Fin (n+1) => ℂ` in
Fin.snoc and Fin.snoc_init_self, resolving the dependent-family metavariable;
remove the sole compiler-reported unused PiLp.toLp_apply in appendVector_norm_sq.
The original snoc decomposition and every mathematical argument remain intact.

Both literal frozen headers and all 13 frozen inputs are unchanged. Original
packet01 is authenticated and remains sealed. Before/after source copies,
exact diff, actual86 receipt/logs and primary-source hashes are preserved here.
No compiler or other validation run was performed by this author; retry and
independent proof review remain pending. No whole-target or Comparator claim.
