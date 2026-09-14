"""Exact finite regression checks, not a proof of the asymptotic open target."""
from fractions import Fraction
from itertools import product, combinations
from math import comb, factorial, gcd, prod
from pathlib import Path
import json
import random
import sys
import unittest

import numpy as np
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
import ac06_round4 as a


def height_one_polynomials(variables=2, degree=2):
    exponents = a.monomials(variables, degree)
    for coefficients in product((-1, 0, 1), repeat=len(exponents)):
        yield {e: c for e, c in zip(exponents, coefficients) if c}


def partitions(k):
    if k == 0:
        yield []
        return
    for old in partitions(k-1):
        yield old + [[k-1]]
        for j in range(len(old)):
            yield [block + ([k-1] if i == j else []) for i, block in enumerate(old)]


def independent_det_mod(matrix, prime):
    """Modular determinant, without normalizing pivot rows."""
    b = np.array(matrix, dtype=np.int64, copy=True) % prime
    if b.ndim != 2 or b.shape[0] != b.shape[1]:
        raise ValueError("square matrix required")
    det = 1
    for j in range(len(b)):
        pivot = next((i for i in range(j, len(b)) if int(b[i,j]) != 0), None)
        if pivot is None:
            return 0
        if pivot != j:
            b[[j,pivot]] = b[[pivot,j]]
            det = -det
        value = int(b[j,j])
        det = det * value % prime
        if j+1 < len(b):
            f = b[j+1:,j].copy() * pow(value,-1,prime) % prime
            b[j+1:,j+1:] = (b[j+1:,j+1:] - f[:,None]*b[j,j+1:][None,:]) % prime
            b[j+1:,j] = 0
    return int(det % prime)


class InterpolationCompactionTests(unittest.TestCase):
    def test_01_exhaustive_height_one_preservation(self):
        points = [[0,0],[1,0],[0,1]]
        output = a.compact_list(points,2)["point"]
        checked = 0
        for p in height_one_polynomials():
            if any(a.evaluate(p,s) for s in points):
                self.assertNotEqual(a.evaluate(p,output),0)
                checked += 1
        self.assertEqual(checked,702)

    def test_02_exact_example(self):
        result = a.compact_list([[0,0],[1,0],[0,1]],2)
        self.assertEqual(result["base"],3457)
        self.assertEqual(result["point"],[-11943935,5973696])
        self.assertTrue(all(isinstance(x,int) for x in result["point"]))
        self.assertEqual(result["guarantee"],"BOUNDED_CERTIFICATE_PRESERVATION_ONLY")

    def test_03_constant_polynomials_and_many_nodes(self):
        result = a.compact_list([[i,i*i] for i in range(8)],0)
        self.assertGreaterEqual(result["base"],8)
        self.assertEqual(a.evaluate({(0,0):-1},result["point"]),-1)

    def test_04_one_candidate(self):
        point = [3,-5,0]
        self.assertEqual(a.compact_list([point],4,7)["point"],point)

    def test_05_repeated_candidates(self):
        output = a.compact_list([[2,-3]]*5,2)["point"]
        self.assertEqual(output,[2,-3])

    def test_06_negative_entries_and_height_three(self):
        points = [[-3,2],[4,-1],[-1,-2]]
        output = a.compact_list(points,2,3)["point"]
        rng = random.Random(904)
        for _ in range(100):
            p = {e:rng.randint(-3,3) for e in a.monomials(2,2)}
            if any(a.evaluate(p,s) for s in points):
                self.assertNotEqual(a.evaluate(p,output),0)

    def test_07_interpolation_node_identity_and_l1_bound(self):
        t = sp.Symbol("t")
        for length in range(2,8):
            points = [[(-1)**j*(j+1),j*j-2] for j in range(length)]
            q = factorial(length-1)
            c = max(abs(v) for row in points for v in row)*2**(length-1)*factorial(length)
            for coordinate in range(2):
                f = sp.Poly(sum((-1)**(length-1-j)*comb(length-1,j)*points[j][coordinate]
                                *prod(t-m for m in range(length) if m!=j)
                                for j in range(length)),t)
                self.assertLessEqual(sum(abs(int(v)) for v in f.all_coeffs()),c)
                for j in range(length):
                    self.assertEqual(f.eval(j),q*points[j][coordinate])

    def test_08_integer_lagrange_weights(self):
        for length in range(2,9):
            q = factorial(length-1)
            for b in range(length,length+6):
                for h in range(length):
                    numerator = (-1)**(length-1-h)*comb(length-1,h)*prod(b-m for m in range(length) if m!=h)
                    integer = (-1)**(length-1-h)*comb(b,h)*comb(b-h-1,length-1-h)
                    self.assertEqual(numerator,q*integer)

    def test_09_rational_input(self):
        points = [[Fraction(1,2),Fraction(-2,3)], [Fraction(-1,5),Fraction(4,7)]]
        output = a.compact_rational(points,2)["point"]
        self.assertTrue(all(isinstance(x,Fraction) for x in output))
        for p in height_one_polynomials():
            if any(a.evaluate(p,s) for s in points):
                self.assertNotEqual(a.evaluate(p,output),0)

    def test_10_invalid_inputs(self):
        for points in ([],[[]],[[1],[1,2]],[[1.0,2]],[[True,0]]):
            with self.assertRaises(ValueError):
                a.compact_list(points,2)
        for d,h in ((-1,1),(2,0),(False,1)):
            with self.assertRaises(ValueError):
                a.compact_list([[1]],d,h)
        with self.assertRaises(ValueError):
            a.compact_rational([[0.1]],2)

    def test_11_output_guard(self):
        with self.assertRaises(ValueError):
            a.compact_list([[1,2],[3,4]],10,max_output_bits=20)

    def test_12_common_zero_not_promised(self):
        points = [[0,0],[1,0],[0,1]]
        polynomial = {(1,1):1}
        self.assertTrue(all(a.evaluate(polynomial,s)==0 for s in points))
        # It may or may not survive; the theorem does not assume it vanishes.
        self.assertEqual(a.compact_list(points,2)["guarantee"],"BOUNDED_CERTIFICATE_PRESERVATION_ONLY")


class ChineseRemainderCompactionTests(unittest.TestCase):
    def test_13_pairwise_coprime_factorial_bases(self):
        for length in range(1,31):
            bases = [1+j*factorial(length) for j in range(1,length+1)]
            self.assertTrue(all(gcd(x,y)==1 for x,y in combinations(bases,2)))

    def test_14_residues_and_modulus_bounds(self):
        points = [[-2,3],[4,-5],[0,2],[8,1]]
        result = a.compact_crt(points,3,2)
        for row,m in zip(points,result["moduli"]):
            self.assertGreater(m,result["evaluation_bound"])
            self.assertTrue(all((v-x)%m==0 for v,x in zip(result["point"],row)))
        self.assertTrue(all(0<=v<result["modulus"] for v in result["point"]))

    def test_15_exhaustive_height_one_preservation(self):
        points = [[0,0],[1,0],[0,1]]
        result = a.compact_crt(points,2)
        for p in height_one_polynomials():
            if any(a.evaluate(p,s) for s in points):
                self.assertNotEqual(a.evaluate(p,result["point"]),0)

    def test_16_constant_certificate(self):
        result = a.compact_crt([[0],[1],[2]],0,7)
        for c in range(-7,8):
            self.assertEqual(a.evaluate({(0,):c},result["point"]),c)

    def test_17_evaluation_bound(self):
        rng = random.Random(1301)
        points = [[rng.randint(-3,3) for _ in range(3)] for _ in range(4)]
        result = a.compact_crt(points,3,2)
        for _ in range(40):
            p = {e:rng.randint(-2,2) for e in a.monomials(3,3)}
            for row in points:
                self.assertLessEqual(abs(a.evaluate(p,row)),result["evaluation_bound"])

    def test_18_guard_and_single_point(self):
        with self.assertRaises(ValueError):
            a.compact_crt([[1,2],[3,4]],5,max_output_bits=4)
        result=a.compact_crt([[-3,4]],2)
        for p in height_one_polynomials():
            if a.evaluate(p,[-3,4]):
                self.assertNotEqual(a.evaluate(p,result["point"]),0)


class CurveTests(unittest.TestCase):
    def test_19_exhaustive_nonzero_pullbacks(self):
        for weights in ([0,0],[0,1],[1,1],[1,2],[2,3]):
            result=a.specialize_monomial_curve(weights,2)
            for p in height_one_polynomials():
                if a.substitute_weights(p,weights):
                    self.assertNotEqual(a.evaluate(p,result["point"]),0)

    def test_20_no_odd_unique_minimum_needed(self):
        polynomial={(1,0):1,(0,1):1,(1,1):-1}
        self.assertEqual(a.substitute_weights(polynomial,[1,1]),{1:2,2:-1})
        self.assertEqual(a.evaluate(polynomial,[2,2]),0)
        result=a.specialize_monomial_curve([1,1],2)
        self.assertEqual(result["base"],7)
        self.assertEqual(a.evaluate(polynomial,result["point"]),-35)

    def test_21_identically_zero_pullback(self):
        p={(1,0):1,(0,1):-1}
        self.assertEqual(a.substitute_weights(p,[1,1]),{})
        self.assertEqual(a.evaluate(p,a.specialize_monomial_curve([1,1],1)["point"]),0)

    def test_22_first_nonzero_coefficient_modulo_base(self):
        for bound in range(1,5):
            b=bound+1
            for coeffs in product(range(-bound,bound+1),repeat=3):
                if any(coeffs):
                    self.assertNotEqual(sum(c*b**j for j,c in enumerate(coeffs)),0)

    def test_23_tensor_rank_one_equation(self):
        p={(1,0,0,1,0,0,0,0):1,(0,1,1,0,0,0,0,0):-1}
        result=a.specialize_monomial_curve([0,0,0,1,0,0,0,0],2)
        self.assertEqual(result["base"],46)
        self.assertEqual(a.evaluate(p,result["point"]),45)

    def test_24_invalid_and_guard(self):
        for w in ([],[-1],[False]):
            with self.assertRaises(ValueError):
                a.specialize_monomial_curve(w,2)
        with self.assertRaises(ValueError):
            a.specialize_monomial_curve([100,200],2,max_output_bits=10)


class ColoringCeilingTests(unittest.TestCase):
    def test_25_block_binomial_inequality(self):
        for n in range(1,36):
            for t in range(1,n+1):
                for p in range(n-t+1):
                    left=comb(n,p+t)*comb(n,p)
                    right=comb(n,t)*comb(n-t,p)**2
                    self.assertLessEqual(left,right)

    def test_26_binomial_endpoint_minimum(self):
        for n in range(1,31):
            for t in range(1,n+1):
                values=[comb(p+t,t)*comb(n-p,t) for p in range(n-t+1)]
                self.assertEqual(min(values),comb(n,t))

    def test_27_all_small_partition_dimensions(self):
        for k in (1,2,3):
            for modes in product(list(partitions(k)),repeat=3):
                for shifts_kind in (0,1,2):
                    n=4
                    shifts=[[0 if shifts_kind==0 else (n-len(b) if shifts_kind==1 else (n-len(b))//2)
                             for b in mode] for mode in modes]
                    data=a.kronecker_koszul_data(n,modes,shifts)
                    self.assertLessEqual(data["dimension_product"],data["rank_cost"]**2*data["binomial_product"])
                    self.assertLessEqual(data["binomial_product"],n**(3*k))
                    self.assertLessEqual(data["maximum_degree"],3*(n-1))
                    self.assertLessEqual(data["pattern_ceiling"],data["uniform_ceiling"])

    def test_28_greedy_coloring_lower_bound(self):
        for k in range(1,4):
            for modes in product(list(partitions(k)),repeat=3):
                data=a.kronecker_koszul_data(3,modes,[[0]*len(m) for m in modes])
                delta=data["maximum_degree"]
                for q in range(delta+1,delta+4):
                    self.assertGreaterEqual(a.count_colorings(k,data["edges"],q),(q-delta)**k)

    def test_29_every_classical_flattening_small_examples(self):
        examples=[([[0]],[[0]],[[0]]), ([[0,1]],[[0],[1]],[[0],[1]])]
        for modes in examples:
            shifts=[[min(1,3-len(b)) for b in mode] for mode in modes]
            data=a.kronecker_koszul_data(3,modes,shifts)
            q=data["dimension_pattern_ceiling"]
            threshold=a.count_colorings(data["power"],data["edges"],q)*data["rank_cost"]
            dims=data["dimensions"]
            for mask in range(1<<len(dims)):
                rows=prod(d for i,d in enumerate(dims) if mask>>i&1)
                cols=data["dimension_product"]//rows
                self.assertLessEqual(min(rows,cols),threshold)

    def test_30_tangency_pattern(self):
        modes=[[[0,1]],[[0],[1]],[[0],[1]]]
        data=a.kronecker_koszul_data(6,modes,[[1],[0,0],[0,0]])
        self.assertEqual(data["rank_cost"],4)
        self.assertEqual(data["edges"],[(0,1)])
        for q in range(1,8):
            self.assertEqual(a.count_colorings(2,data["edges"],q),q*(q-1))

    def test_31_linear_iteration_arithmetic(self):
        for n in range(1,101):
            for k in range(1,6):
                delta=3*(n-1)
                q=11*n-3
                self.assertEqual((q-delta)**k,(8*n)**k)
                self.assertEqual(11*n-3,8*n+delta)

    def test_32_large_n_uses_linear_ceiling(self):
        data=a.kronecker_koszul_data(100,[[[0]],[[0]],[[0]]],[[0],[0],[0]])
        self.assertEqual(data["elementary_uniform_ceiling"],1297)
        self.assertEqual(data["linear_iteration_uniform_ceiling"],1097)
        self.assertEqual(data["uniform_ceiling"],1097)
        self.assertEqual(data["pattern_ceiling"],800)

    def test_33_invalid_patterns(self):
        cases=[(2,[[[0]],[[0]]],[[0],[0]]),
               (2,[[[0,1,2]],[[0,1,2]],[[0,1,2]]],[[0],[0],[0]]),
               (2,[[[0]],[[0]],[[1]]],[[0],[0],[0]])]
        for args in cases:
            with self.assertRaises(ValueError):
                a.kronecker_koszul_data(*args)


class FiniteTensorCertificateTests(unittest.TestCase):
    def test_34_modular_rank_vs_small_exact_matrices(self):
        rng=random.Random(41)
        for rows,cols in ((1,1),(3,4),(4,3),(6,6)):
            for _ in range(8):
                m=np.array([[rng.randrange(-4,5) for _ in range(cols)] for _ in range(rows)],dtype=np.int64)
                data=a.modular_rank_certificate(m,65521)
                self.assertLessEqual(data["rank_mod_prime"],sp.Matrix(m.tolist()).rank())
                minor=m[np.ix_(data["minor_rows"],data["minor_columns"])]
                self.assertNotEqual(independent_det_mod(minor,65521),0)

    def test_35_independent_modular_determinant(self):
        rng=random.Random(9)
        for size in range(1,7):
            for _ in range(8):
                m=[[rng.randint(-7,7) for _ in range(size)] for _ in range(size)]
                self.assertEqual(independent_det_mod(m,101),int(sp.Matrix(m).det())%101)

    def test_36_pure_tensor_koszul_cost(self):
        for n in range(2,7):
            weights=[i+2*j+3*k for k in range(n) for j in range(n) for i in range(n)]
            for p in range(n):
                m=a.koszul_matrix_mod(n,p,65521,weights)
                self.assertEqual(a.modular_rank_certificate(m,65521)["rank_mod_prime"],comb(n-1,p))

    def test_37_shifted_weights_and_output_bound(self):
        for n in range(1,31):
            weights=a.shifted_weights(n)
            self.assertEqual(len(weights),n**3)
            self.assertGreaterEqual(min(weights),0)
            self.assertLess(max(weights),4*n**4)

    def test_38_saved_candidate_minors(self):
        expected={2:(2,2),3:(8,4),4:(15,5),5:(45,8),6:(84,9),7:(224,12),8:(420,12),9:(1050,15)}
        root=Path(__file__).resolve().parents[1]/"evidence"
        for n,(rank,lower) in expected.items():
            data=json.loads((root/f"shifted_n{n}_p65521.json").read_text())
            self.assertEqual(data["rank_mod_prime"],rank)
            self.assertEqual(data["certified_border_rank_lower_bound"],lower)
            m=a.koszul_matrix_mod(n,data["exterior_degree"],65521,a.shifted_weights(n))
            minor=m[np.ix_(data["minor_rows"],data["minor_columns"])]
            self.assertNotEqual(independent_det_mod(minor,65521),0)

    def test_39_other_prime_crosscheck(self):
        for n in range(2,7):
            first=a.shifted_certificate(n,65521)
            second=a.shifted_certificate(n,65519)
            self.assertEqual(first["rank_mod_prime"],second["rank_mod_prime"])

    def test_40_guards_and_scope(self):
        with self.assertRaises(ValueError):
            a.modular_rank_certificate([[1.5]],65521)
        with self.assertRaises(ValueError):
            a.monomials(20,20)
        with self.assertRaises(ValueError):
            a.koszul_matrix_mod(3,1,15,a.shifted_weights(3))
        with self.assertRaises(ValueError):
            a.koszul_matrix_mod(10,4,65521,a.shifted_weights(10))
        with self.assertRaises(ValueError):
            a.koszul_matrix_mod(3,3,65521,a.shifted_weights(3))
        self.assertIn("NOT_QUADRATIC",a.shifted_certificate(2)["scope"])


if __name__=="__main__":
    unittest.main(verbosity=2)
