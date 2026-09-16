import NLA.IV03.Adjugate
import LeanCert.Tactic.IntervalAuto.PointIneq
set_option leancert.trust "kernel"
#assert_trust kernel NLA.IV03.complementary_principal_minor_split
#print axioms NLA.IV03.complementary_principal_minor_split
#assert_trust kernel NLA.IV03.inverse_principal_det_neg
#print axioms NLA.IV03.inverse_principal_det_neg
#assert_trust kernel NLA.IV03.rank_le_one_two_minor_zero
#print axioms NLA.IV03.rank_le_one_two_minor_zero
#assert_trust kernel NLA.IV03.zMatrix_positive_diagonal_rank_gt_one
#print axioms NLA.IV03.zMatrix_positive_diagonal_rank_gt_one
#assert_trust kernel NLA.IV03.adjugate_nonsingular
#print axioms NLA.IV03.adjugate_nonsingular
#assert_trust kernel NLA.IV03.adjugate_det_pos_of_diagonal
#print axioms NLA.IV03.adjugate_det_pos_of_diagonal
#assert_trust kernel NLA.IV03.adjugate_completion
#print axioms NLA.IV03.adjugate_completion
#assert_trust kernel NLA.IV03.inverseM_of_proper_principal_and_adjugate
#print axioms NLA.IV03.inverseM_of_proper_principal_and_adjugate
