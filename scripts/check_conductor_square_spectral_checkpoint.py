#!/usr/bin/env python3
"""Exact arithmetic guards for the conductor-square research checkpoint.

Run: python3 -B scripts/check_conductor_square_spectral_checkpoint.py

Standard library only. These tests do NOT prove L-depth, spectral moment
inputs, the archimedean transform, global reciprocity, or any zero-free result.
Polynomial equality checks are symbolic; sampled Fraction/matrix checks are
explicitly finite regression checks.
"""

from fractions import Fraction as F
from itertools import product
import unittest


class Poly:
    """Small exact Q[x,y] used only for denominator-cleared identities."""

    def __init__(self, terms=0):
        if isinstance(terms, Poly):
            terms = terms.terms
        elif not isinstance(terms, dict):
            terms = {(0, 0): F(terms)}
        self.terms = {k: F(v) for k, v in terms.items() if v}

    def __add__(self, other):
        result = dict(self.terms)
        for key, value in Poly(other).terms.items():
            result[key] = result.get(key, F(0)) + value
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + -Poly(other)

    def __rsub__(self, other):
        return Poly(other) + -self

    def __mul__(self, other):
        result = {}
        for (a, b), v in self.terms.items():
            for (c, d), w in Poly(other).terms.items():
                key = (a + c, b + d)
                result[key] = result.get(key, F(0)) + v * w
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, n):
        if not isinstance(n, int) or n < 0:
            raise ValueError("only nonnegative integer powers are supported")
        result = Poly(1)
        for _ in range(n):
            result = result * self
        return result

    def __eq__(self, other):
        return self.terms == Poly(other).terms

    def __repr__(self):
        return repr(self.terms)


def unramified(r, z):
    h, ell = 1 - r, 1 + r + z
    c1 = (7 - r - z) / ell
    c2 = (-z**3 + (7-r)*z**2 + (9*r-21)*z + r*r-20*r+27) / (h*ell)
    return c1, c2


def deep_cells(r, z):
    """Evaluate the infinite geometric cell sums by exact closed moments."""
    s = 1 + r - z
    e0 = 1/s
    e1 = (z-2*r)/s**2
    e2 = (z-4*r)/s**2 + 2*(z-2*r)**2/s**3

    def cell(v, k):
        return F(v+1, 2)*(e2+(2*k+v+3)*e1+(k+1)*(k+v+2)*e0)

    def tail(m):
        # cell(m+j,0) is a quadratic in j, recovered by finite differences.
        c = cell(m, 0)
        a = (cell(m+2, 0)-2*cell(m+1, 0)+c)/2
        b = cell(m+1, 0)-c-a
        return c/(1-r)+b*r/(1-r)**2+a*r*(1+r)/(1-r)**3

    h, ell = 1-r, 1+r+z
    c0 = s**3*tail(0)
    c1 = s**3*(tail(1)+(cell(0, 0)+cell(0, 1))/ell)
    c2 = s**3*(tail(2)+(cell(1, 0)+cell(1, 1))/ell
                   +(cell(0, 0)+(1-z-r)*cell(0, 1)+cell(0, 2))/(h*ell))
    return c0, c1, c2


def matmul(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(3))
             for j in range(3)] for i in range(3)]


class CheckpointChecks(unittest.TestCase):
    def test_polynomial_engine(self):
        x, y = Poly({(1, 0): 1}), Poly({(0, 1): 1})
        self.assertEqual((x+y)**2, x*x+2*x*y+y*y)
        self.assertNotEqual(x+y, x-y)
        self.assertEqual((x+1)*(x-1), x*x-1)
        self.assertEqual(x-x, 0)
        with self.assertRaises(ValueError):
            x**-1

    def test_unramified_cancellation_symbolic(self):
        r, z = Poly({(1, 0): 1}), Poly({(0, 1): 1})
        numerator = -z**3+(7-r)*z**2+(9*r-21)*z+r*r-20*r+27
        pnum = -z*z+8*z+2*r-22
        self.assertEqual(numerator-(7+r)*(7-r-z), (1+r+z)*pnum)
        self.assertNotEqual(numerator-(7+r)*(7-r-z), (1+r+z)*(pnum+1))

    def test_gram_inverse_constant_vector_symbolic(self):
        r, z = Poly({(1, 0): 1}), Poly({(0, 1): 1})
        # Clear denominators from G_2^{-1}1=(1+r)/(h*ell)*(1,h-z,1).
        gram_num = [[1+r, z, z*z-r-r*r],
                    [z, 1+r, z], [z*z-r-r*r, z, 1+r]]
        vector = [Poly(1), 1-r-z, Poly(1)]
        for row in gram_num:
            self.assertEqual(sum(a*b for a, b in zip(row, vector)),
                             (1-r)*(1+r+z))
        self.assertEqual((1+r)+z, 1+r+z)  # Depth-one row sum.

    def test_hecke_test_telescopes_symbolic(self):
        root, t = Poly({(1, 0): 1}), Poly({(0, 1): 1})
        lambdas = [Poly(1), t]
        for _ in range(2, 9):
            lambdas.append(t*lambdas[-1]-lambdas[-2])
        total = Poly(1)
        for m in range(1, 9):
            total += root**m*lambdas[m]-root**(m-1)*lambdas[m-1]
            self.assertEqual(total, root**m*lambdas[m])

    def test_physical_hecke_vector_symbolic(self):
        r, z = Poly({(1, 0): 1}), Poly({(0, 1): 1})
        a0 = 9*r-r*r-22
        # B D1=(8-r)(z-r), r^2 D2=z^2-r(1+z).
        self.assertEqual(a0+(8-r)*(z-r)-z*z+r*(1+z), -z*z+8*z+2*r-22)

    def test_dual_remainder_coefficient_symbolic(self):
        r = Poly({(1, 0): 1})
        # Clear (1-r^2) in b*h-B+r^2*(a-b)=2*K*h.
        lhs = -8*r*(1-r)-r*(8-r)*(1-r*r)+r*r*(7+r*r+8*r)
        self.assertEqual(lhs, 16*r*(r*r+r-1))

    def test_steinberg_rows_symbolic(self):
        r = Poly({(1, 0): 1})
        for sign in (-1, 1):
            with self.subTest(sign=sign):
                self.assertEqual((7-sign*r)*(1-r*r),
                                 (7+r*r-8*r*sign)*(1+sign*r))
                # Clear h*(1-r^2) in the dual conductor-one row.
                lhs = 8*r*sign*(1-r)-r*(8-r)*(1-r*r)+r*r*(7+r*r-8*r*sign)
                self.assertEqual(lhs, 8*r*(r*r+r-1)*(1-sign))

    def test_cells_and_dual_fraction_samples(self):
        primes = (2, 3, 5, 7, 11, 13, 17)
        zs = (F(-1, 2), F(-1, 3), F(-1, 7), F(0), F(1, 7), F(1, 3), F(1, 2))
        for p, z in product(primes, zs):
            with self.subTest(p=p, z=z):
                r = F(1, p)
                h = 1-r
                c1, c2 = unramified(r, z)
                self.assertEqual(deep_cells(r, z), (F(1), c1, c2))
                a, b = (7+r*r)/(1-r*r), -8*r/(1-r*r)
                a0, b0 = 9*r-r*r-22, r*(8-r)
                d1, d2 = z/r-1, z*z/r**2-(1+z)/r
                pweight = (-z*z+8*z+2*r-22)/h
                self.assertEqual((a0+b0*d1-r*r*d2)/h, pweight)
                self.assertEqual((c2-a*c1+b*c1-pweight)/h, 0)
                dual = (d2-a*d1+b*c1)/h-(a0+b0*c1-r*r*c2)/h**2
                kappa = 8*r*(r*r+r-1)/(h*(1-r*r))
                main = (z*z/r**2-1/r-8*z/(r*(1-r*r)))/h
                remainder = a/h-a0/h**2+r*r*pweight/h**2+2*kappa*c1/h
                self.assertEqual(dual, main+remainder)

    def test_ramified_fraction_samples_and_sign(self):
        for p in (2, 3, 5, 7, 11, 13, 17):
            r, h = F(1, p), 1-F(1, p)
            a, b = (7+r*r)/(1-r*r), -8*r/(1-r*r)
            b0, kappa = r*(8-r), 8*r*(r*r+r-1)/(h*(1-r*r))
            self.assertLess(kappa, 0)
            self.assertEqual(r*r/h, F(1, p*(p-1)))
            self.assertLessEqual(r*r/h, F(1, 2))
            for sign in (-1, 1):
                with self.subTest(p=p, sign=sign):
                    c1, c2, cj = h, h*(7-sign*r)/(1+sign*r), sign*h
                    self.assertEqual((c2-a*c1-b*cj)/h, 0)
                    self.assertEqual(-b*cj/h-(b0*c1-r*r*c2)/h**2, kappa*(1-sign))

    def test_matrix_package_samples(self):
        w23 = [[1, 0, 0], [0, 0, 1], [0, 1, 0]]
        k0 = [[0, -1, 0], [0, 0, 1], [1, 0, 0]]
        for p in (2, 3, 5, 7, 11):
            jinv = [[0, F(-1, p), 0], [1, 0, 0], [0, 0, 1]]
            for b in range(p):
                with self.subTest(p=p, b=b):
                    g = [[F(1, p), 0, 0], [0, 1, 0], [0, F(b, p), 1]]
                    u13 = [[1, 0, F(b, p)], [0, 1, 0], [0, 0, 1]]
                    self.assertEqual(matmul(matmul(w23, jinv), u13), matmul(g, k0))
                    if b:
                        kb = [[1, 0, 0], [0, p, F(1, b)], [0, -b, 0]]
                        lhs = [[p*v for v in row] for row in matmul(g, kb)]
                        self.assertEqual(lhs, [[1, 0, 0], [0, p*p, F(p, b)], [0, 0, 1]])

    def test_interpolation_symbolic(self):
        t = Poly({(1, 0): 1})
        # alpha=(1-2t)/(4+4t); 1-alpha=(3+6t)/(4+4t).
        a, b = 1-2*t, 3+6*t
        self.assertEqual(-3*a*(1+2*t)+b*(1-2*t), 0)  # D exponent
        self.assertEqual(-3*a*(1+2*t)-b*(1+2*t), -6*(1+2*t))  # E
        self.assertEqual(3*a*(1+2*t)+b*(3+2*t), 12+24*t)  # C, with X outside

    def test_interpolation_fraction_samples(self):
        for i in range(64):
            t = F(i, 128)
            alpha = (1-2*t)/(4+4*t)
            with self.subTest(theta=t):
                self.assertGreaterEqual(alpha, 0)
                self.assertLessEqual(alpha, 1)
                self.assertEqual(-alpha*(1+2*t)+(1-alpha)*(1-2*t)/3, 0)
                self.assertEqual(-alpha*(1+2*t)-(1-alpha)*(1+2*t)/3,
                                 -(1+2*t)/(2+2*t))
                self.assertEqual(alpha*(1+2*t)+(1-alpha)*(1+2*t/3), 1+t/(1+t))
        t = F(7, 64)
        self.assertEqual((1-2*t)/(4+4*t), F(25, 142))
        self.assertEqual(t/(1+t), F(7, 71))
        self.assertEqual(2*t/3, F(7, 96))

    def test_gamma_recurrence_pair_polynomials(self):
        # This checks the shift polynomials, not analytic gamma bounds.
        a, t = Poly({(1, 0): 1}), Poly({(0, 1): 1})
        for depth in range(6):
            pair, real, imag = Poly(1), Poly(1), Poly(0)
            for j in range(depth+1):
                pair *= (a+2*j)**2+t*t
                # Independently multiply all plus factors in Q[x,y][i].
                real, imag = real*(a+2*j)-imag*t, real*t+imag*(a+2*j)
            # The minus-factor product is the conjugate; norm is multiplicative.
            self.assertEqual(pair, real*real+imag*imag)
            # Adjoint pair: (1+2j)^2+4t^2 = 4*((j+1/2)^2+t^2).
            adj, scaled = Poly(1), Poly(1)
            for j in range(depth+1):
                adj *= (1+2*j)**2+4*t*t
                scaled *= F((2*j+1)**2, 4)+t*t
            self.assertEqual(adj, 4**(depth+1)*scaled)


if __name__ == "__main__":
    unittest.main(verbosity=2)
