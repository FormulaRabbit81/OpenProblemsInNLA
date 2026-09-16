import NLA.IV03.IntervalAdjugate
import LeanCert.Tactic.IntervalAuto.PointIneq
set_option leancert.trust "kernel"
#assert_trust kernel NLA.IV03.interval_schur_nonnegative
#print axioms NLA.IV03.interval_schur_nonnegative
#assert_trust kernel NLA.IV03.interval_adjugate_nonpositive
#print axioms NLA.IV03.interval_adjugate_nonpositive
#assert_trust kernel NLA.IV03.inverseM_empty
#print axioms NLA.IV03.inverseM_empty
