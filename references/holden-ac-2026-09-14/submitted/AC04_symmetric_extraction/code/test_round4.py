"""Regression and corruption checks for the new exact certificates."""
from fractions import Fraction as Q
from itertools import product
import unittest
from exact import (rational,I,power23,icbrt,rank_exact,rank_mod,matmul,transpose,
                   nullspace,determinant,inverse2,kron,contraction,U)
import verify as v
import symmetric_extraction as s

class ArithmeticTests(unittest.TestCase):
    def test_rational_input(self): self.assertEqual(rational('7/3'),Q(7,3))
    def test_reject_float(self):
        with self.assertRaises(TypeError): rational(0.5)
    def test_reject_complex(self):
        with self.assertRaises(TypeError): rational(1j)
    def test_reject_boolean(self):
        with self.assertRaises(TypeError): rational(True)
    def test_integer_cube_root(self):
        for n in range(400):
            k=icbrt(n);self.assertLessEqual(k**3,n);self.assertGreater((k+1)**3,n)
    def test_cube_root_interval(self):
        a=power23(Q(110,2));self.assertLess(a.lo**3,3025);self.assertGreater(a.hi**3,3025)
    def test_exact_cube(self): self.assertEqual(power23(8),I.point(4))
    def test_interval_square_across_zero(self): self.assertEqual(I(-3,2).square(),I(0,9))
    def test_reversed_interval(self):
        with self.assertRaises(ValueError): I(1,0)
    def test_nullspace(self):
        A=[[1,2,3],[2,4,6]];K=nullspace(A)
        self.assertEqual(len(K),2);self.assertEqual(matmul(A,transpose(K)),[[0,0],[0,0]])
    def test_inverse(self): self.assertEqual(matmul([[2,1],[1,3]],inverse2([[2,1],[1,3]])),[[1,0],[0,1]])
    def test_determinant_corruption(self):
        A=[[8,4,4,2],[4,2,8,4],[4,8,2,4],[2,4,4,8]]
        self.assertEqual(determinant(A),-1296);A[1]=A[0][:];self.assertEqual(determinant(A),0)
    def test_modular_rank_is_only_lower_bound(self):
        self.assertEqual(rank_exact([[101]]),1);self.assertEqual(rank_mod([[101]]),0)
    def test_reject_noninteger_modular_input(self):
        with self.assertRaises(TypeError): rank_mod([[Q(1,2)]])

class ExtractionTests(unittest.TestCase):
    def test_first_power_edge_case(self):
        a=s.audit_maps(1);self.assertEqual((a['s'],a['t'],a['limit_terms']),(2,0,6))
    def test_second_power(self):
        a=s.audit_maps(2);self.assertEqual((a['r'],a['s'],a['t']),(16,4,2))
    def test_third_power(self):
        a=s.audit_maps(3);self.assertEqual((a['r'],a['s'],a['t']),(64,8,18))
    def test_fourth_power(self):
        a=s.audit_maps(4);self.assertEqual((a['r'],a['s'],a['t']),(256,16,110))
        b=s.direct_border_padding(4);self.assertEqual(b['rank_one_terms'],274)
        self.assertEqual(b['maximum_tensor_polynomial_degree'],9)
        self.assertEqual(a['group_source_terms_checked'],65536);self.assertEqual(a['limit_terms'],1626)
    def test_missing_padding_rejected(self):
        with self.assertRaises(ArithmeticError): s.audit_maps(2,padding_sign=0)
    def test_wrong_padding_sign_rejected(self):
        with self.assertRaises(ArithmeticError): s.audit_maps(2,padding_sign=1)
    def test_bad_power_rejected(self):
        with self.assertRaises(ValueError): s.audit_maps(0)
    def test_complex_congruence(self): self.assertEqual(s.gaussian_congruence()['QQ_transpose'],[[0,1],[1,0]])
    def test_cw_border_formula(self):
        for q in [2,4,8,16]: self.assertEqual(s.cw_border(q)['limit_terms'],3*q)
    def test_tight_support_marginals(self):
        a=s.entropy_support(110);self.assertEqual(a['support_size'],330)
        self.assertEqual(a['marginals'][0]['0'],Q(1,3));self.assertEqual(a['marginals'][0]['1'],Q(1,165))
    def test_odd_tight_parameter_rejected(self):
        with self.assertRaises(ValueError): s.entropy_support(3)
    def test_new_bound_bracket(self):
        a=s.algebraic_bound();self.assertGreater(Q(a['lower_bracket_polynomial_gap']),0)
        self.assertLess(Q(a['upper_bracket_polynomial_gap']),0)
    def test_false_display_bound_rejected_by_sign(self):
        a=Q('3.89');self.assertGreater((274-a**4)**3-81675,0)

class RigidityTests(unittest.TestCase):
    def test_standard_identity(self): self.assertEqual(v.standard_certificate()['tensor_coefficients_checked'],729)
    def test_tangent_dimensions(self):
        a=v.tangent_certificate();self.assertEqual((a['symmetric_jacobian_rank'],a['unrestricted_jacobian_rank']),(128,384))
    def test_charge_00(self):
        rows,E=v.charge_block((0,0));self.assertEqual((len(rows),rank_exact(E)),(6,5))
    def test_single_charge(self):
        for t in [(i,0) for i in range(1,4)]+[(0,i) for i in range(1,4)]:
            rows,E=v.charge_block(t);self.assertEqual((len(rows),rank_exact(E)),(7,7))
    def test_double_charge(self):
        for t in product(range(1,4),repeat=2):
            rows,E=v.charge_block(t);self.assertEqual((len(rows),rank_exact(E)),(13,9))
    def test_mixed_obstruction(self):
        a=v.obstruction_certificate();self.assertEqual(a['number_of_invertible_blocks'],9)
        self.assertTrue(all(x['determinant'] for x in a['blocks']))
    def test_cokernel_corruption_rejected(self):
        _,E=v.charge_block((1,1));K=nullspace(transpose(E));K[0][0]+=1
        self.assertTrue(any(x for row in matmul(K,E) for x in row))
    def test_graph_connectivity(self): self.assertEqual(v.graph_certificate(2)['vertex_pairs_checked'],1332)
    def test_torus_dimensions(self): self.assertEqual(v.torus_certificate()['exponent_ranks'],[10,10,16,42,42,48])
    def test_adaptive_exact_example(self):
        a=v.adaptive_example();self.assertEqual(a['contraction_rank'],4);self.assertGreater(a['weight_array_rank'],1)
    def test_support_inequality(self): self.assertEqual(v.support_certificate()['local_patterns'],81)
    def test_zero_support(self): self.assertEqual(rank_exact(contraction(kron(U,U),[0]*16)),0)
    def test_inherited_bound(self): self.assertGreater(Q(v.inherited_upper()['margin_lower']),0)

if __name__=='__main__': unittest.main(verbosity=2)
