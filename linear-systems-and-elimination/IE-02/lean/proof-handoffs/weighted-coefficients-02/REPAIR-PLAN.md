# WeightedCoefficients02: bounded wrapper repair

Actual local73 exit1 reports exactly the fixed degree-bound cast mismatch and
the generic real-part norm rewrite mismatch. The trust assertion correctly
rejects the resulting sorryAx; no WeightedCoefficients output is accepted.

Before code: replace WithBot.coe_add by Nat.cast_add in the degree simp. The
pinned Polynomial/Degree/Defs.lean:469 proof of natDegree_mul_le performs this
same Nat.cast_add rewrite for its WithBot natural degree bounds. The frozen
bounds use Nat.cast, so the WithBot coercion lemma did not match the written
term. No degree inequality changes.

For the norm conversion, give the identity a fully typed local interface
  (inner ℂ x x).re = norm x squared,
for x in the exact H(d+m+1), proved by norm_sq_eq_re_inner specialized to ℂ and
x. Simplify with this explicit interface instead of rewriting the generic
RCLike real projection. This mirrors root's actual73 successful MaximalSpace
wrapper pattern; it adds no assumption.

Only these proof bodies change. Preserve the exact frozen public header,
private helper statement, imports, trust controls, all 13 frozen inputs and
the immutable original plan/handoff. No compiler or cache command runs here;
retry remains for the sole root compiler.
