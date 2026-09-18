# Observed local101 coordinate elaboration repair

Simplify both conditionals before cases in the X-lift. The cases tactic has
already substituted the coefficient index, so remove the subsequent he
rewrite and its unused zero-branch simp item. Lift q=X*divX(q) by congrArg
at exactly the left polynomial factor, avoiding recursive rewriting inside
divX. Supply Nat.lt_succ_self n to the WithBot strict degree inequality.
All helper headers and the full finrank proof remain unchanged.

Original source and full local101 receipt/logs are retained. Polynomial02
passed actual101; Coordinates failed and has no accepted output. Retry is
UNRUN, root serial compiler only. No frozen input or resource changed.
