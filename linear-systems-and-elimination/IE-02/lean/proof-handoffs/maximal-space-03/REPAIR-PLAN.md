# Maximal-space minimal complex-cast repair

Actual local70 fails only at the generic RCLike real-conjugation rewrite.
The target contains an explicit Complex.ofReal cast, which Lean's generic
RCLike rewrite did not unify. The preceding inner_smul_left and all other
proof branches passed elaboration. The trust assertion correctly rejected
sorryAx from the unresolved goal; MaximalSpace has no accepted output and
DescentGap was blocked, not run.

Before editing, primary Data/Complex/Basic.lean lines 226 and 475 were read.
Replace only RCLike.conj_ofReal and RCLike.re_ofReal_mul with their explicit
Complex counterparts. Retain norm_sq_eq_re_inner and every other proof token,
the exact frozen header, trust assertions, imports and definitions. This is
an API specialization, with no mathematical route or scope change. Root's
next actual serial local check remains necessary. No compiler is run here.
