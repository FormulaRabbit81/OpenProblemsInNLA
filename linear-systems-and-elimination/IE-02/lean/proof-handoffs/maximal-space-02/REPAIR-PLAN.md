# Maximal-space bounded repair, before edits

Scope: only the existing proof body of the exact frozen ordinal-7 contract.
Actual development-69 compiled the candidate with exit code 1. Its authenticated
raw log reports an unknown real-scalar inner-product lemma and a rewrite blocked
by a reducible Set-membership wrapper. The trust assertion correctly rejected
the resulting sorryAx; there is no accepted output for the failed candidate.

1. The guessed unqualified `inner_smul_ofReal_left` is actually a lemma inside
   InnerProductSpace.Core, with a core-specific local inner-product instance;
   it is not the global API needed here. Use global `inner_smul_left` from
   Analysis/InnerProductSpace/Basic.lean:105, RCLike.conj_ofReal:314 and
   RCLike.re_ofReal_mul:222. The scalar product is then in the target order,
   so delete the now-unneeded final commutativity step.
2. Immediately before rewriting the energy in IsMaxOn, explicitly `change`
   the reducible set-membership predicate to its real inequality. Comment
   that this is only the IsMaxOn/filter representation, not a new assertion.

The Gram/Rayleigh mathematical route, all hypotheses, the conclusion, imports,
trust settings and frozen inputs remain unchanged. No compiler, cache, Git or
network command runs in this task. The repair will be an unrun candidate for
root's next serial local check; original maximal-space-01 remains immutable.
