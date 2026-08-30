#!/usr/bin/env python3
"""Finite guards for primitive Euler factors and physical Mellin scaling.

Arithmetic identities are exact. Atomic/quadrature fixtures are NOT smooth
test functions or certified analytic estimates. Complex samples are NOT
asserted zeta zeros. This script proves no contour shift or zero-free bound.
"""

from fractions import Fraction as F
from functools import lru_cache
import itertools
import math
import unittest

from check_cubic_comb_mode_density import divisors, mobius


@lru_cache(None)
def radical(n):
    return math.prod(p for p in divisors(n)
                     if p > 1 and all(p % d for d in range(2, math.isqrt(p) + 1)))


def correction(d, e):
    return mobius(radical(d)) if radical(d) == radical(e) else 0


def local_h(p, u, v):
    a, b = p ** (-u), p ** (-v)
    return 1 - a * b / ((1 - a) * (1 - b))


def weighted_pair_sum(weight, limit, odd=False):
    numbers = range(1, limit + 1, 2 if odd else 1)
    return sum(mobius(r) * mobius(s) * weight(r, s)
               for r in numbers for s in numbers if math.gcd(r, s) == 1)


def profile_real(z):
    # A positive finite atomic Phi fixture; not a C-infinity function.
    return sum(weight * math.cos(2 * math.pi * a * b / z) / abs(z)
               for a, b, weight in ((1.25, 1.5, 1), (1.75, 1.25, 2)))


class PrimitiveEulerChecks(unittest.TestCase):
    def test_finite_primitive_euler_product(self):
        primes = (2, 3, 5)
        series = F(0)
        for assignments in itertools.product((0, 1, 2), repeat=len(primes)):
            r = math.prod(p for p, a in zip(primes, assignments) if a == 1)
            s = math.prod(p for p, a in zip(primes, assignments) if a == 2)
            series += F(mobius(r) * mobius(s), r ** 2 * s ** 3)
        product = math.prod(1 - F(1, p ** 2) - F(1, p ** 3) for p in primes)
        self.assertEqual(series, product)

    def test_odd_reciprocal_zeta_normalization(self):
        primes = (2, 3, 5, 7)
        u, v = 2, 3
        inverse_zetas = math.prod((1 - F(1, p ** u)) * (1 - F(1, p ** v))
                                 for p in primes)
        h_odd = math.prod(1 - F(1, p ** (u + v)) /
                         ((1 - F(1, p ** u)) * (1 - F(1, p ** v)))
                         for p in primes if p != 2)
        reconstructed = inverse_zetas * h_odd / (
            (1 - F(1, 2 ** u)) * (1 - F(1, 2 ** v)))
        expected = math.prod(1 - F(1, p ** u) - F(1, p ** v)
                             for p in primes if p != 2)
        self.assertEqual(reconstructed, expected)
        self.assertNotEqual(inverse_zetas * h_odd, expected)

    def test_complete_two_variable_convolution(self):
        for r in range(1, 46):
            for s in range(1, 46):
                actual = sum(correction(d, e) * mobius(r // d) * mobius(s // e)
                             for d in divisors(r) for e in divisors(s))
                expected = mobius(r) * mobius(s) * int(math.gcd(r, s) == 1)
                self.assertEqual(actual, expected)

    def test_off_diagonal_prime_powers_cannot_be_dropped(self):
        self.assertEqual(correction(2, 4), -1)
        self.assertEqual(correction(6, 12), 1)
        self.assertEqual(correction(6, 10), 0)
        diagonal_only = sum(correction(d, d) * mobius(2 // d) * mobius(4 // d)
                            for d in divisors(2))
        self.assertNotEqual(diagonal_only, mobius(2) * mobius(4))

    def test_local_absolute_coefficient_sum(self):
        a, b, cutoff = F(1, 5), F(1, 7), 7
        finite = 1 + sum(abs(correction(3 ** i, 3 ** j)) * a ** i * b ** j
                         for i in range(1, cutoff + 1)
                         for j in range(1, cutoff + 1))
        geometric = 1 + a * (1 - a ** cutoff) / (1 - a) * (
            b * (1 - b ** cutoff) / (1 - b))
        self.assertEqual(finite, geometric)

    def test_parity_dilation_identity_with_joint_weight(self):
        limit = 41
        def weight(r, s):
            return F(r + 2 * s, 1 + r * s) if r <= limit and s <= limit else F(0)
        original = weighted_pair_sum(weight, limit)
        odd = weighted_pair_sum(weight, limit, odd=True)
        even_r = weighted_pair_sum(lambda r, s: weight(2 * r, s), limit, odd=True)
        even_s = weighted_pair_sum(lambda r, s: weight(r, 2 * s), limit, odd=True)
        self.assertEqual(original, odd - even_r - even_s)
        self.assertNotEqual(original, odd)

    def test_prime_two_can_vanish_at_a_complex_sample_not_a_zero(self):
        beta = 0.75
        gamma = math.acos(2 ** (beta - 1)) / math.log(2)
        point = complex(beta, gamma)  # No assertion that zeta(point) vanishes.
        self.assertLess(abs(1 - 2 ** (-point) - 2 ** (-point.conjugate())), 1e-14)
        self.assertGreater((1 - 3 ** (-point) - 3 ** (-point.conjugate())).real, 0)

    def test_odd_conjugate_correction_positive_and_factorization(self):
        for beta in (2 / 3, 0.8, 0.99):
            for gamma in (0, 14.25, 101):
                u = complex(beta, gamma)
                for p in (3, 5, 7, 11, 101):
                    h = local_h(p, u, u.conjugate())
                    self.assertGreater(h.real, 0)
                    self.assertLess(abs(h.imag), 1e-13)
                    self.assertLess(abs((1 - p ** (-u)) * (1 - p ** (-u.conjugate()))
                                        * h - (1 - p ** (-u) - p ** (-u.conjugate()))), 1e-13)
        self.assertLess(8, 9)  # Exact cubed threshold: 2 * 3^(-2/3) < 1.

    def test_positive_kernel_does_not_make_arithmetic_positive(self):
        self.assertEqual(math.gcd(15, 17), 1)
        self.assertEqual(mobius(15) * mobius(17), -1)

    def test_profile_evenness_and_positive_subpacket(self):
        for z in (32, 36, 48, 64):
            self.assertAlmostEqual(profile_real(z), profile_real(-z))
            self.assertGreaterEqual(profile_real(z), 3 / (math.sqrt(2) * z) - 1e-14)

    def test_physical_packet_normalization_and_argument(self):
        xscale, yscale, r, s = 1000, 100, 1701, 1500
        hl = xscale * yscale
        delta = F(yscale, xscale)
        x, y = F(r, xscale), F(s, xscale)
        self.assertEqual(F(hl, xscale * s) * F(s * s, hl), y)
        self.assertEqual((x - y) * y / delta, F((r - s) * s, hl))

    def test_thin_band_jacobian_cancels_only_one_y(self):
        y, z, delta = F(3, 2), F(40), F(1, 1000)
        x = y + delta * z / y
        u, v = 3, 4
        weight = y * (1 + x * x) * (1 + y)
        transformed = weight * x ** (u - 1) * y ** (v - 1) * delta / y
        expected = delta * (1 + x * x) * (1 + y) * x ** (u - 1) * y ** (v - 1)
        self.assertEqual(transformed, expected)
        self.assertNotEqual(transformed, expected * y)

    def test_even_profile_cancels_first_taylor_term_exactly(self):
        # Polynomial integrand and atomic y,z samples: an exact algebra guard.
        y, delta = F(3, 2), F(1, 1000)
        zs = ((F(36), F(2)), (F(48), F(1)))
        def f(x):
            return x ** 4 + x ** 2
        total = sum(weight * (f(y + delta * z / y) + f(y - delta * z / y))
                    for z, weight in zs)
        expected = sum(weight * (2 * f(y) + 2 * (6 * y * y + 1) * (delta * z / y) ** 2
                                 + 2 * (delta * z / y) ** 4) for z, weight in zs)
        self.assertEqual(total, expected)
        self.assertGreater(total, sum(2 * weight * f(y) for z, weight in zs))

    def test_complex_sample_has_cubic_remainder_not_identically_real(self):
        point = complex(0.8, 7)  # An arbitrary complex sample, not a zeta zero.
        y = 1.5
        zs = ((36, 2), (48, 1))
        def value(delta):
            return delta * sum(weight * (1 + x * x) * x ** (point - 1)
                               * y ** (point.conjugate() - 1)
                               for z, weight in zs for sign in (-1, 1)
                               for x in (y + sign * delta * z / y,))
        coefficient = 6 * (1 + y * y) * y ** (2 * point.real - 2)
        d1, d2 = 1e-3, 5e-4
        error1, error2 = value(d1) - d1 * coefficient, value(d2) - d2 * coefficient
        self.assertGreater(abs(value(d1).imag), 1e-8)
        self.assertTrue(7.8 < abs(error1 / error2) < 8.2)

    def test_symmetric_weight_has_same_finite_sum(self):
        weight = lambda r, s: F(r + 3 * s, 1 + r * s)
        sym = lambda r, s: (weight(r, s) + weight(s, r)) / 2
        self.assertEqual(weighted_pair_sum(weight, 23, odd=True),
                         weighted_pair_sum(sym, 23, odd=True))

    def test_axis_subtraction_keeps_supported_primitive_sum(self):
        original, centered = F(0), F(0)
        for r in range(1, 32, 2):
            for s in range(1, 32, 2):
                coeff = mobius(r) * mobius(s) * int(math.gcd(r, s) == 1)
                off_axis = (coeff - mobius(r) * int(s == 1)
                            - mobius(s) * int(r == 1) + int(r == s == 1))
                if r == 1 or s == 1:
                    self.assertEqual(off_axis, 0)
                else:
                    self.assertEqual(off_axis, coeff)
                weight = F(r + 2 * s, 1 + r * s) if min(r, s) > 5 else F(0)
                original += coeff * weight
                centered += off_axis * weight
        self.assertEqual(original, centered)

    def test_mellin_phase_coordinates(self):
        y, a, delta, t, tp = 1.5, -17, 1e-3, 78, -75
        x = y * (1 + delta * a)
        self.assertAlmostEqual(t * math.log(x) + tp * math.log(y),
                               (t + tp) * math.log(y) + t * math.log(1 + delta * a))

    def test_local_residue_exponent_is_not_absolute_contour_exponent(self):
        beta = F(2, 3)
        local_exponent = 2 * beta - F(1, 3)
        self.assertEqual(local_exponent, 1)
        self.assertEqual(3 * local_exponent, 3)
        self.assertEqual(2 * beta, F(4, 3))
        self.assertGreater(2 * F(14, 17) - F(1, 3), 1)


if __name__ == "__main__":
    unittest.main()
