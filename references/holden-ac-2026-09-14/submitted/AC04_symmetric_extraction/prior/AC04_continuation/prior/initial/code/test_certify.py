"""Regression tests for exact interval and recurrence implementation."""
from fractions import Fraction as F
import unittest
from certify import Interval, icbrt, cbrt_interval, dimensions, normalized_p, certify


class ExactChecks(unittest.TestCase):
    def test_integer_cube_root(self):
        for n in range(1000):
            r=icbrt(n)
            self.assertLessEqual(r**3,n)
            self.assertLess(n,(r+1)**3)
        for n in [10**100,10**101+1234567,(123456789123456789)**3]:
            r=icbrt(n)
            self.assertLessEqual(r**3,n)
            self.assertLess(n,(r+1)**3)

    def test_cube_root_bounds(self):
        for n in [0,1,2,7,8,9,18**2,1782**2,240734740800726**2]:
            x=cbrt_interval(n,20)
            self.assertLessEqual(x.lo**3,n)
            self.assertLessEqual(n,x.hi**3)
            self.assertLessEqual(x.hi-x.lo,F(1,10**20))

    def test_interval_square(self):
        self.assertEqual(Interval(F(-2),F(3)).square(),Interval(F(0),F(9)))
        self.assertEqual(Interval(F(-3),F(-2)).square(),Interval(F(4),F(9)))
        self.assertEqual(Interval(F(2),F(3)).square(),Interval(F(4),F(9)))

    def test_closed_form(self):
        for n in range(3,10):
            for j,(d,t,M) in enumerate(dimensions(n,4)):
                a=4**n+2**n
                b=a-3*3**n
                self.assertEqual(d,(a**(2**j)-b**(2**j))//3)
                self.assertEqual(t,(a**(2**j)+2*b**(2**j))//3)
                self.assertEqual(2*d+t,M)

    def test_known_dimensions(self):
        self.assertEqual(dimensions(3,2),[(27,18,72),(1701,1782,5184),
                                      (8955765,8962326,26873856)])

    def test_monotonicity_in_tensor_value(self):
        # Regression check, not the analytic all-parameter proof.
        a=normalized_p(F('3.92'),3)
        b=normalized_p(F('3.923038'),3)
        self.assertLess(a.hi,b.lo)

    def test_certificate(self):
        self.assertIn('PASS',certify()['status'])

    def test_bad_inputs(self):
        for f in [lambda: icbrt(-1),lambda:cbrt_interval(-1),lambda:dimensions(2,1),
                  lambda:Interval(F(2),F(1)),lambda:normalized_p(F(3),1,n=4)]:
            with self.assertRaises(ValueError):
                f()


if __name__ == '__main__':
    unittest.main(verbosity=2)
