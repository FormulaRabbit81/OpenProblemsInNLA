"""Regression and deliberate-corruption tests for the finite certificate code."""
import unittest
from fractions import Fraction as Q
from exact import *
from verify import (adaptive_example,block_degeneration,check_cosets,parameters,conditional_target,
                    pencil_local_checks,require,upper_bound)

class ExactTests(unittest.TestCase):
    def test_integer_cube_roots(self):
        for n in range(300):
            k=icbrt(n);self.assertLessEqual(k**3,n);self.assertGreater((k+1)**3,n)
    def test_large_cube_roots(self):
        n=10**100+1234567;k=icbrt(n)
        self.assertLessEqual(k**3,n);self.assertGreater((k+1)**3,n)
    def test_fractional_root_intervals(self):
        for x in (Q(0),Q(1),Q(8),Q(27),Q(4,7),Q(12345,17)):
            a=power23(x);self.assertLessEqual(a.lo**3,x*x);self.assertGreaterEqual(a.hi**3,x*x)
    def test_interval_squaring_across_zero(self):
        self.assertEqual(I(-2,3).square(),I(0,9))
    def test_bad_interval_rejected(self):
        with self.assertRaises(ValueError):I(2,1)
    def test_float_certificate_data_rejected(self):
        with self.assertRaises(TypeError):I.point(3.95)
    def test_rational_rank(self):
        self.assertEqual(rank_exact([[1,Q(1,2)],[2,1]]),1)
    def test_modular_rank_lower_bound(self):
        a=[[101,0],[0,1]]
        self.assertEqual(rank_mod(a),1);self.assertEqual(rank_exact(a),2)
    def test_local_harmonic_condition(self):
        self.assertEqual(rank_exact(local_h([1,2,3,Q(-6,11)])),2)
        self.assertEqual(rank_exact(local_h([1,2,3,1])),3)
    def test_pure_factorization(self):
        fs=[[1,2,3,4],[2,5,7,9]];w=tensor_weights(fs)
        self.assertIsNotNone(pure_factors(w,2))
    def test_corrupted_factor_certificate_rejected(self):
        w=tensor_weights([[1,2,3,4],[2,5,7,9]]);w[0]+=1
        self.assertIsNone(pure_factors(w,2))
    def test_zero_weight_excluded(self):
        w=[1]*16;w[0]=0;self.assertIsNone(pure_factors(w,2))
    def test_incorrect_shape_rejected(self):
        with self.assertRaises(ValueError):pure_factors([1]*15,2)
    def test_walsh_direct(self):
        w=list(range(1,17));A=kronecker_power(V,2)
        self.assertEqual(sign_matrix(w,2),contraction(A,w))
    def test_minimum_sign_counts(self):
        for n in (1,2,3,4):self.assertEqual(len(set(map(tuple,character_signs(n)))),2*3**n)
    def test_single_flip_rank(self):
        w=next(character_signs(3));w[3]=-w[3]
        self.assertEqual(rank_exact(sign_matrix(w,3)),9)
    def test_block_harmonic_equality_noncommuting(self):
        A=[[2,1],[1,1]];B=[[3,2],[1,3]]
        self.assertNotEqual(matmul(A,B),matmul(B,A))
        neg=lambda X:[[-x for x in r] for r in X]
        blocks=[A,B,neg(A)];D=neg(B)
        R=[[blocks[i//2][i%2][j%2]+D[i%2][j%2] if i//2==j//2 else D[i%2][j%2]
            for j in range(6)] for i in range(6)]
        self.assertEqual(rank_exact(R),4)
    def test_adaptive_nonproduct_identity(self):
        a=adaptive_example();self.assertEqual(a['contraction_rank'],4);self.assertEqual(a['weight_matrix_rank'],2)
    def test_coset_formulas(self):
        for n in range(1,5):
            for k in range(1,n+1):check_cosets(n,k)
    def test_two_slice_map(self):
        self.assertEqual(block_degeneration(4,1)['negative_degree_terms'],0)
    def test_pencil_border_identity(self):
        self.assertEqual(pencil_local_checks()['path_border_terms'],3)
    def test_bad_parameters(self):
        with self.assertRaises(ValueError):parameters(3,4)
    def test_old_upper_recertified(self):
        self.assertEqual(upper_bound()['upper_bound'],'3923037967879/1000000000000')
    def test_conditional_certificate_is_labeled(self):
        self.assertIn("NOT_SUPPLIED",conditional_target()["status"])
    def test_corrupted_claim_rejected(self):
        with self.assertRaises(ArithmeticError):require(Q(79,20)==3,'False equality')

if __name__=='__main__':unittest.main(verbosity=2)
