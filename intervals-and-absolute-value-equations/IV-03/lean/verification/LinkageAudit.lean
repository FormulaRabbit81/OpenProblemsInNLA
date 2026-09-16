import NLA.IV03.IntervalStructure
import LeanCert.Tactic.IntervalAuto.PointIneq
set_option leancert.trust "kernel"
#assert_trust kernel NLA.IV03.adjugate_fromBlocks_two_offdiag
#print axioms NLA.IV03.adjugate_fromBlocks_two_offdiag
#assert_trust kernel NLA.IV03.adjugate_two_schur_split
#print axioms NLA.IV03.adjugate_two_schur_split
#assert_trust kernel NLA.IV03.inverse_difference_identity
#print axioms NLA.IV03.inverse_difference_identity
#assert_trust kernel NLA.IV03.matrix_mul_nonnegative
#print axioms NLA.IV03.matrix_mul_nonnegative
#assert_trust kernel NLA.IV03.schur_bilinear_difference
#print axioms NLA.IV03.schur_bilinear_difference
#assert_trust kernel NLA.IV03.schur_bilinear_monotone
#print axioms NLA.IV03.schur_bilinear_monotone
#assert_trust kernel NLA.IV03.vertex_principal
#print axioms NLA.IV03.vertex_principal
#assert_trust kernel NLA.IV03.interval_principal
#print axioms NLA.IV03.interval_principal
#assert_trust kernel NLA.IV03.proper_principal_transfer
#print axioms NLA.IV03.proper_principal_transfer
