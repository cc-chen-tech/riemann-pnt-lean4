#!/usr/bin/env python3
"""Finite guards for difference-frequency normalization and primitive costs.

No zeta zeros are computed or excluded. Finite frequency examples do not
prove an infinite-height limit or identify a Besicovitch completion with
the meromorphic zeta quotient. Gaussian fixtures test Fourier conventions,
not the punctured compact support theorem, which is proved in the note.
"""

import cmath
from fractions import Fraction as Q
import itertools
import math
import unittest


def mobius_table(limit):
    values = [1] * (limit + 1)
    values[0] = 0
    composite = [False] * (limit + 1)
    for p in range(2, limit + 1):
        if not composite[p]:
            for n in range(p, limit + 1, p):
                composite[n] = True
                values[n] *= -1
            for n in range(p * p, limit + 1, p * p):
                values[n] = 0
    return values


def midpoint(fn, left, right, count=10000):
    step = (right - left) / count
    return step * sum(fn(left + (j + 0.5) * step) for j in range(count))


def sinc(x):
    return 1.0 if x == 0 else math.sin(x) / x


def gram(frequencies, coefficients, length):
    return sum(a * b.conjugate() * sinc(length * (x - y))
               for x, a in zip(frequencies, coefficients)
               for y, b in zip(frequencies, coefficients))


class DifferencePrimitiveChecks(unittest.TestCase):
    def test_prime_square_union_constant_is_strictly_positive(self):
        upper = Q(1, 4) + Q(1, 9) + Q(1, 25) + Q(1, 49) + Q(1, 14)
        self.assertEqual(upper, Q(21739, 44100))
        self.assertEqual(1 - 2 * upper, Q(311, 22050))
        self.assertLess(upper, Q(1, 2))

    def test_adjacent_squarefree_count_finite_union_bound(self):
        mu = mobius_table(200001)
        for scale in (100, 1000, 10000, 100000):
            good = sum(mu[n] != 0 and mu[n + 1] != 0
                       for n in range(scale, 2 * scale))
            lower = float(Q(311, 22050)) * scale - 2 * math.sqrt(2 * scale + 1)
            self.assertGreaterEqual(good, lower)
            self.assertGreater(good, scale / 5)

    def test_coprime_nonzero_frequencies_are_injective(self):
        pairs = [(r, s) for r in range(1, 65) for s in range(1, 65)
                 if r != s and math.gcd(r, s) == 1]
        self.assertEqual(len(pairs), len({Q(r, s) for r, s in pairs}))

    def test_without_coprimality_the_frequencies_collide(self):
        self.assertEqual(Q(2, 3), Q(4, 6))
        self.assertNotEqual((2, 3), (4, 6))
        self.assertNotEqual(math.gcd(4, 6), 1)

    def test_coprime_zero_frequency_is_only_one_one(self):
        diagonal = [(r, s) for r in range(1, 40) for s in range(1, 40)
                    if r == s and math.gcd(r, s) == 1]
        self.assertEqual(diagonal, [(1, 1)])

    def test_square_norm_finite_euler_product(self):
        # sigma=1: exact rational norm; 0/1/2 assigns each prime to neither/r/s.
        primes = (2, 3, 5, 7)
        total = Q(0)
        for choices in itertools.product((0, 1, 2), repeat=len(primes)):
            r = math.prod(p for p, choice in zip(primes, choices) if choice == 1)
            s = math.prod(p for p, choice in zip(primes, choices) if choice == 2)
            self.assertEqual(math.gcd(r, s), 1)
            total += Q(1, (r * s) ** 2)
        self.assertEqual(total, math.prod(1 + Q(2, p * p) for p in primes))

    def test_finite_primitive_derivative_has_correct_sign(self):
        mu = mobius_table(20)
        sigma, omega, gamma, t = 0.8, 1.25, 7.5, 0.9
        for r, s in ((2, 3), (5, 6), (7, 10), (11, 13)):
            frequency = math.log(r / s)
            coefficient = mu[r] * mu[s] * (r * s) ** (-sigma - 1j * (gamma + omega / 2))
            primitive = coefficient / (-1j * frequency)
            derivative = -1j * frequency * primitive * cmath.exp(-1j * t * frequency)
            self.assertLess(abs(derivative - coefficient * cmath.exp(-1j * t * frequency)), 1e-14)

    def test_common_height_twist_preserves_squared_norm(self):
        for r, s in ((2, 3), (5, 6), (7, 10)):
            frequency, sigma = math.log(r / s), 2 / 3
            untwisted = (r * s) ** (-sigma) / (-1j * frequency)
            twisted = untwisted * (r * s) ** (-1j * 123.5)
            self.assertAlmostEqual(abs(untwisted) ** 2, abs(twisted) ** 2)

    def test_near_diagonal_log_bounds(self):
        for n in (2, 7, 31, 1000):
            for w in range(1, n + 1):
                self.assertLessEqual(1 / math.log1p(w / n), 2 * n / w)
            self.assertLessEqual(math.log1p(1 / n), 1 / n)

    def test_exact_threshold_and_endpoint_exponents(self):
        self.assertEqual(2 - 4 * Q(3, 4), -1)
        self.assertEqual(3 - 4 * Q(3, 4), 0)
        self.assertEqual(Q(3, 2) - 2 * Q(2, 3), Q(1, 6))
        self.assertLess(2 - 4 * Q(4, 5), -1)

    def test_primitive_growth_cost_retains_positive_theta(self):
        for theta in (Q(0), Q(1, 10), Q(1, 2), Q(1)):
            exponent = 2 * Q(2, 3) - (1 - theta) / 3
            self.assertEqual(exponent, 1 + theta / 3)
        self.assertGreater(1 + Q(1, 30), 1)

    def test_repeated_primitives_have_stricter_thresholds(self):
        for order in range(1, 8):
            threshold = Q(order, 2) + Q(1, 4)
            self.assertEqual(2 * order - 4 * threshold, -1)
            self.assertEqual(2 * order + 1 - 4 * threshold, 0)
        self.assertEqual(Q(2, 2) + Q(1, 4), Q(5, 4))

    def test_logarithmic_coordinate_jacobians(self):
        # (log x,log y)=(p+d/2,p-d/2); (t1,t2)=(omega/2+t,omega/2-t).
        self.assertEqual(abs(Q(1) * Q(-1, 2) - Q(1, 2) * Q(1)), 1)
        self.assertEqual(abs(Q(1, 2) * Q(-1) - Q(1) * Q(1, 2)), 1)

    def test_actual_kernel_support_gives_logarithmic_hole(self):
        for delta in (1e-5, 1e-4, 1e-3):
            for y in (1.2, 1.5, 1.8):
                for z in (-63, -40, 40, 63):
                    x = y + delta * z / y
                    self.assertTrue(1 < x < 2)
                    ratio = abs(math.log(x / y)) / delta
                    self.assertGreater(ratio, 8)
                    self.assertLess(ratio, 64)

    def test_fourier_moment_normalization_gaussian_fixture(self):
        # f(d)=exp(-(d-a)^2) is NOT the punctured kernel.
        a = 0.7
        values = (1, 2 * a, 4 * a * a - 2, 8 * a ** 3 - 12 * a)
        for order, derivative_factor in enumerate(values):
            integral = midpoint(lambda t: t ** order * math.sqrt(math.pi)
                                * math.exp(-t * t / 4) * cmath.exp(1j * a * t), -16, 16)
            expected = 2 * math.pi * 1j ** order * derivative_factor * math.exp(-a * a)
            self.assertLess(abs(integral - expected), 1e-10)

    def test_actual_annulus_excludes_adjacent_pairs_at_large_scale(self):
        scale = 10 ** 9
        delta = scale ** (-1 / 3)
        for n in (scale, 3 * scale // 2, 2 * scale - 1):
            self.assertLess(math.log1p(1 / n), 8 * delta)
        self.assertEqual(2 - 4 * Q(2, 3) + Q(1, 3), Q(-1, 3))

    def test_finite_annular_primitive_norm_upper_bound(self):
        scale, delta, lower, upper, sigma = 100, 0.05, 1, 3, 2 / 3
        mu = mobius_table(2 * scale)
        pairs = [(r, s) for r in range(scale, 2 * scale + 1)
                 for s in range(scale, 2 * scale + 1)
                 if lower * delta <= abs(math.log(r / s)) <= upper * delta]
        self.assertLessEqual(len(pairs), (scale + 1) * (4 * scale * upper * delta + 2))
        norm2 = sum(mu[r] ** 2 * mu[s] ** 2 / ((r * s) ** (2 * sigma) * math.log(r / s) ** 2)
                    for r, s in pairs if math.gcd(r, s) == 1)
        self.assertLessEqual(norm2, len(pairs) * scale ** (-4 * sigma) / (lower * delta) ** 2)

    def test_finite_gram_identity_includes_offdiagonal(self):
        frequencies = [math.log(3 / 2), math.log(5 / 3), math.log(7 / 4)]
        coefficients = [complex(1, 2), complex(-2, 1), complex(0.5, -1)]
        length = 4
        exact = gram(frequencies, coefficients, length)
        quadrature = midpoint(lambda t: abs(sum(a * cmath.exp(-1j * t * x)
                                               for x, a in zip(frequencies, coefficients))) ** 2,
                              -length, length) / (2 * length)
        self.assertLess(abs(exact - quadrature), 1e-7)
        self.assertGreater(abs(exact - sum(abs(a) ** 2 for a in coefficients)), 1)

    def test_dense_frequency_block_is_not_short_window_orthogonal(self):
        count, length = 40, 100
        frequencies = [1 + j / (10 * length * count) for j in range(count)]
        exact = gram(frequencies, [1 + 0j] * count, length).real
        self.assertGreaterEqual(exact, math.cos(0.1) * count ** 2)
        self.assertGreater(exact, 30 * count)

    def test_cluster_residue_cancels_inverse_gap(self):
        # A(z)=2+3z+5z^2+7z^3, exact two-pole sum for rational eps.
        polynomial = lambda z: 2 + 3 * z + 5 * z ** 2 + 7 * z ** 3
        for eps in (Q(1, 2), Q(1, 10), Q(1, 1000)):
            combined = (polynomial(eps) - polynomial(-eps)) / (2 * eps)
            self.assertEqual(combined, 3 + 7 * eps ** 2)
        self.assertEqual(3 + 7 * Q(0) ** 2, 3)

    def test_double_cluster_mixed_divided_difference(self):
        # A(u,v)=1+2u+3v+5uv+7u^3 v+11u v^3+13u^2 v^2.
        polynomial = lambda u, v: 1 + 2 * u + 3 * v + 5 * u * v + 7 * u ** 3 * v + 11 * u * v ** 3 + 13 * u ** 2 * v ** 2
        eps, eta = Q(1, 100), Q(1, 50)
        numerator = sum(a * b * polynomial(a * eps, b * eta)
                        for a in (-1, 1) for b in (-1, 1))
        self.assertEqual(numerator / (4 * eps * eta), 5 + 7 * eps ** 2 + 11 * eta ** 2)


if __name__ == "__main__":
    unittest.main(verbosity=2)
