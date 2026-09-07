#!/usr/bin/env python3
"""Finite normalization checks for the cubic comb note, not an analytic proof.

Run directly with Python 3; only the standard library is required.
The MRSTT theorem, smooth-kernel hypotheses and asymptotic estimates are
mathematical inputs, not claims established by these finite checks.
"""

import cmath
from fractions import Fraction as F
import math
import unittest


def primes(n):
    result = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            result.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        result.append(n)
    return result


def mobius(n):
    factors = primes(n)
    if any(n % (p * p) == 0 for p in factors):
        return 0
    return (-1) ** len(factors)


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def g(d):
    return math.prod(F(p, p + 1) for p in primes(d))


def b(a, n):
    return math.prod(F(1, p + 1) for p in primes(n) if a % p)


def exp2pi(z):
    return cmath.exp(2j * math.pi * z)


def convolution_weight(q, kappa, n):
    """h_{Q,kappa}; prime-power exponents do not change the local value."""
    return math.prod(
        F(1) if q % p == 0 else (F(1, p + 1) if kappa else F(0))
        for p in primes(n)
    )


def ramanujan(s, n):
    return sum(d * mobius(s // d) for d in divisors(s) if n % d == 0)


def kloosterman(s, a, b):
    return sum(exp2pi(F(a * z + b * pow(z, -1, s), s))
               for z in range(s) if math.gcd(z, s) == 1)


def gaussian_poisson(a, r, n, kl, sign=-1, jacobian=True):
    """Schwartz regression kernel phi(y)=exp(-pi*y*y)*e(y/3).

    The modulation makes the sign check nonvacuous; an even real Gaussian
    would not distinguish the two Fourier phase conventions.
    """
    step = r * n / a
    center = kl / step
    left = sum(
        math.exp(-math.pi * (step * c - kl) ** 2)
        * exp2pi((step * c - kl) / 3)
        for c in range(math.floor(center - 9 / step) - 1,
                       math.ceil(center + 9 / step) + 2)
    )
    mode_step = 1 / step
    right = sum(
        math.exp(-math.pi * (j * mode_step - 1 / 3) ** 2)
        * exp2pi(sign * j * mode_step * kl)
        for j in range(math.floor((-9 + 1 / 3) / mode_step) - 1,
                       math.ceil((9 + 1 / 3) / mode_step) + 2)
    )
    return left, right * (mode_step if jacobian else 1)


class CubicCombChecks(unittest.TestCase):
    def test_taylor_uniform_margin(self):
        eps, nu = F(1, 1000), F(17, 50)
        coefficient = 4 * (1 - nu) * (1 - eps) - 2
        self.assertGreater(coefficient, 0)
        # The saving is affine in u and decreasing in p; its minimum is
        # therefore at u=1/2, p=2u, without a sampled-polytope assumption.
        u = F(1, 2)
        xmin = (u - eps) * (1 - eps)
        self.assertEqual(xmin, F(498501, 1000000))
        saving = 4 * (1 - nu) * xmin - eps - 2 * u
        self.assertEqual(saving, F(3938033, 12500000))
        self.assertGreater(saving, 0)
        self.assertEqual(nu - (F(1, 3) + eps), F(17, 3000))
        self.assertEqual(1 - eps - nu, F(659, 1000))

    def test_exact_parameters_and_prefactor(self):
        for a in (1, 3, 19, 200):
            for e in (1, 2, 7):
                for r in (1, 5, 11):
                    s = F(1001)
                    d, x = s / e, s / (e * r)
                    h = a / d
                    prefactor = F(a, r * r * e * e) / x
                    self.assertEqual(prefactor * (1 + 1 / h),
                                     F(a, r * e) / s + F(1, r * e * e))
                    for j in (-5, 0, 4):
                        for kl in (-11, 0, 6):
                            lam = j * h
                            self.assertEqual(lam * x * kl, F(j * a * kl, r))

    def test_modulated_gaussian_poisson(self):
        for args in ((3, 2, 7, 1), (1, 1, 41, 2), (17, 1, 2, -3),
                     (7, 3, 11, 0), (2, 1, 13, -1)):
            with self.subTest(args=args):
                left, right = gaussian_poisson(*args)
                self.assertLess(abs(left - right), 2e-12)

    def test_poisson_sign_and_jacobian_mutants_rejected(self):
        args = (3, 2, 7, 1)
        left, wrong_sign = gaussian_poisson(*args, sign=1)
        _, wrong_factor = gaussian_poisson(*args, jacobian=False)
        self.assertGreater(abs(left - wrong_sign), 0.01)
        self.assertGreater(abs(left - wrong_factor), 0.01)

    def test_mode_density_integral_bound(self):
        # Finite partial sums verify the normalization, not the infinite
        # integral-comparison proof given in the note.
        for h in (0.003, 0.05, 0.8, 1.0, 7.0, 101.0):
            for order in (2, 3, 5):
                partial = 1 + 2 * math.fsum(
                    (1 + j * h) ** (-order) for j in range(1, 20001)
                )
                self.assertLessEqual(partial, 1 + 2 / (h * (order - 1)))

    def test_tail_density_first_point_bound(self):
        # Includes h>cutoff, where dropping the first lattice point would
        # make the usual tail integral comparison unjustified.
        for h in (0.003, 0.2, 2.0, 10.0, 101.0):
            for cutoff in (1.0, 3.0, 17.0):
                for order in (2, 3, 5):
                    start = math.floor(cutoff / h) + 1
                    partial = 2 * math.fsum(
                        (1 + j * h) ** (-order)
                        for j in range(start, start + 5000)
                    )
                    bound = 2 * (1 + cutoff) ** (-order)
                    bound += 2 * (1 + cutoff) ** (1 - order) / (h * (order - 1))
                    self.assertLessEqual(partial, bound)

    def test_sliding_window_weights(self):
        x = F(20)
        for y in (F(7, 3), F(4), F(9, 2)):
            for n in range(20, 41):
                length = max(F(0), min(F(n), 2 * x - y) - max(F(n) - y, x))
                if x + y <= n <= 2 * x - y:
                    self.assertEqual(length / y, 1)
                self.assertGreaterEqual(length, 0)
                self.assertLessEqual(length, y)

    def test_euler_complete_and_truncated_identities(self):
        for n in range(1, 101):
            for a in (1, 2, 6, 17):
                terms = {d: mobius(d) * g(d) for d in divisors(n)
                         if math.gcd(d, a) == 1}
                self.assertEqual(sum(terms.values()), b(a, n))
                for cutoff in (1, 3, 11, 31):
                    truncated = sum(v for d, v in terms.items() if d <= cutoff)
                    tail = sum(v for d, v in terms.items() if d > cutoff)
                    self.assertEqual(truncated, b(a, n) - tail)
                    weight = lambda d: max(F(0), 1 - F(d, 2 * cutoff))
                    smooth = sum(v * weight(d) for d, v in terms.items())
                    correction = sum(v * (1 - weight(d)) for d, v in terms.items())
                    self.assertEqual(smooth, b(a, n) - correction)

    def test_prime_truncation_witness(self):
        prime, cutoff, a = 101, 10, 6
        terms = {d: mobius(d) * g(d) for d in divisors(prime)
                 if math.gcd(d, a) == 1}
        truncated = sum(v for d, v in terms.items() if d <= cutoff)
        tail = sum(v for d, v in terms.items() if d > cutoff)
        self.assertEqual(truncated, 1)
        self.assertEqual(b(a, prime), F(1, 102))
        self.assertEqual(tail, -F(101, 102))
        self.assertNotEqual(truncated, b(a, prime) + tail)
        self.assertNotEqual(truncated, b(a, prime))

    def test_smooth_support_euler_bound(self):
        for q in range(1, 101):
            phi = q * math.prod(F(p - 1, p) for p in primes(q))
            total = sum(
                F(mobius(d) ** 2, 1)
                / (d * math.prod(F(p - 1, p) for p in primes(d)))
                for d in divisors(q)
            )
            self.assertEqual(total, F(q) / phi)
            harmonic_bound = sum(F(len(divisors(d)), d) for d in range(1, q + 1))
            self.assertLessEqual(total, harmonic_bound)
            self.assertLessEqual(float(harmonic_bound), (1 + math.log(q)) ** 2 + 1e-12)

    def test_frequency_axes_are_not_product_volume(self):
        # With one nonzero-frequency range empty, the axes still survive.
        kmax, lmax = F(1, 4), F(100)
        k = math.floor(kmax)
        ell = math.floor(lmax)
        nonzero_pairs = 4 * k * ell
        axes = 1 + 2 * k + 2 * ell
        self.assertEqual(nonzero_pairs, 0)
        self.assertEqual(axes, 201)
        self.assertGreater(axes, 4 * kmax * lmax)

    def test_coprime_density_convolution(self):
        for n in range(1, 121):
            for q in (1, 2, 6, 35):
                for kappa in (0, 1):
                    actual = sum(mobius(n // r) * convolution_weight(q, kappa, r)
                                 for r in divisors(n))
                    expected = mobius(n) * (g(n) if kappa else 1)
                    if math.gcd(n, q) != 1:
                        expected = 0
                    self.assertEqual(actual, expected)

    def test_density_convolution_not_restricted_to_q_smooth(self):
        self.assertEqual(convolution_weight(6, 0, 25), 0)
        self.assertEqual(convolution_weight(6, 1, 25), F(1, 6))
        self.assertEqual(convolution_weight(6, 1, 12), 1)

    def test_euler_convolution_mass_at_one(self):
        prime_list = [p for p in range(2, 101) if primes(p) == [p]]
        for q in (1, 2, 6, 35, 60):
            euler_zero = math.prod(F(p, p - 1) for p in primes(q))
            for kappa in (0, 1):
                partial_product = math.prod(
                    1 + convolution_weight(q, kappa, p) / (p - 1)
                    for p in prime_list
                )
                if kappa == 0:
                    self.assertEqual(partial_product, euler_zero)
                else:
                    zeta_two_product = math.prod(F(p * p, p * p - 1)
                                                 for p in prime_list)
                    exact_product = zeta_two_product * math.prod(
                        F(p + 1, p) for p in primes(q)
                    )
                    self.assertEqual(partial_product, exact_product)
                    self.assertLess(partial_product, 2 * euler_zero)

    def test_rankin_convolution_tail(self):
        for q in (1, 6, 35):
            for kappa in (0, 1):
                for cutoff in (2, 7, 31):
                    tail = sum(float(convolution_weight(q, kappa, r)) / r
                               for r in range(cutoff + 1, 201))
                    half_moment = sum(float(convolution_weight(q, kappa, r))
                                      / math.sqrt(r) for r in range(1, 201))
                    self.assertLessEqual(tail, half_moment / math.sqrt(cutoff))
        self.assertEqual(F(499, 1000) * F(1, 2000), F(499, 2000000))

    def test_large_convolution_integer_endpoints(self):
        for d in (F(7, 3), F(10), F(37, 2)):
            for r in range(1, math.floor(2 * d) + 1):
                count = sum(d < r * n < 2 * d
                            for n in range(1, math.ceil(2 * d) + 1))
                self.assertLessEqual(count, d / r + 1)
                self.assertLessEqual(d / r + 1, 3 * d / r)

    def test_ramanujan_cofactor_weight_preserves_both_denominators(self):
        for s in range(1, 81):
            for n in range(-3, 13):
                left = F(mobius(s) * ramanujan(s, n), s * s)
                right = sum(
                    F(mobius(d), d) * F(mobius(s // d) ** 2, (s // d) ** 2)
                    for d in divisors(s)
                    if n % d == 0 and math.gcd(d, s // d) == 1
                )
                self.assertEqual(left, right)

    def test_extra_modulus_inverse_mutant_rejected(self):
        # s=S=5, n=1: the exact coefficient is 1/25, not 1/125.
        s, n = 5, 1
        left = F(mobius(s) * ramanujan(s, n), s * s)
        cofactor = sum(
            F(mobius(d), d) * F(mobius(s // d) ** 2, (s // d) ** 2)
            for d in divisors(s)
            if n % d == 0 and math.gcd(d, s // d) == 1
        )
        self.assertEqual(left, F(1, 25))
        self.assertEqual(left, cofactor)
        self.assertNotEqual(left, cofactor / s)

    def test_discrete_double_completion_with_modulus_weight(self):
        # DFT normalization replaces the continuous HL lengths with the
        # actual Fourier coefficients, retaining the same two s factors.
        for s in (3, 5, 6, 7):
            a = 1
            u = [F((2 * h + 1) % 5, 5) for h in range(s)]
            v = [F((h * h + 2) % 7, 7) for h in range(s)]
            uf = [sum(u[h] * exp2pi(F(-k * h, s)) for h in range(s))
                  for k in range(s)]
            vf = [sum(v[h] * exp2pi(F(-ell * h, s)) for h in range(s))
                  for ell in range(s)]
            original = F(mobius(s), s) * sum(
                u[h] * v[d] * kloosterman(s, a, -h * d)
                for h in range(s) for d in range(s)
            )
            completed = F(mobius(s), s * s) * sum(
                uf[k] * vf[ell] * ramanujan(s, a + k * ell)
                for k in range(s) for ell in range(s)
            )
            self.assertLess(abs(original - completed), 2e-12)


if __name__ == "__main__":
    unittest.main(verbosity=2)
