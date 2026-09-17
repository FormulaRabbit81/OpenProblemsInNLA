import NLA.IV03.Principal
import LeanCert.Tactic.IntervalAuto.PointIneq
set_option leancert.trust "kernel"
#assert_trust kernel NLA.IV03.inverseM_principal_split
#print axioms NLA.IV03.inverseM_principal_split
#assert_trust kernel NLA.IV03.inverseM_principal
#print axioms NLA.IV03.inverseM_principal
#assert_trust kernel NLA.IV03.inverseM_principal_det_pos
#print axioms NLA.IV03.inverseM_principal_det_pos
#assert_trust kernel NLA.IV03.inverseM_schur_split
#print axioms NLA.IV03.inverseM_schur_split
#assert_trust kernel NLA.IV03.inverseM_cross_transfer_nonnegative
#print axioms NLA.IV03.inverseM_cross_transfer_nonnegative
#assert_trust kernel NLA.IV03.inverseM_transpose
#print axioms NLA.IV03.inverseM_transpose
#assert_trust kernel NLA.IV03.inverseM_left_transfer_nonnegative
#print axioms NLA.IV03.inverseM_left_transfer_nonnegative
