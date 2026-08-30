#!/usr/bin/env python3
"""Finite checks for joint-mode/squarefree-quotient reassembly.

These standard-library regressions verify arithmetic and discrete Fourier
normalization, not the continuous Poisson theorem or any analytic bound on
the full physical moment. Run this file directly with Python 3.
"""

from fractions import Fraction as F
import math
import unittest

from check_cubic_comb_mode_density import (
    divisors, exp2pi, kloosterman, mobius, primes, ramanujan,
)


def type_terms(n, cutoff):
    return [(a, b, n // (a * b), mobius(a) * mobius(b))
            for a in divisors(n) if a <= cutoff
            for b in divisors(n // a)
            if n // b > cutoff and mobius(a) * mobius(b)]


def mu_square_convolution(n):
    return sum(mobius(a) * mobius(n // a) for a in divisors(n))


def coprime_part(n, q):
    for p in primes(q):
        while n % p == 0:
            n //= p
    return n


def sample_weight(n, length):
    if not length < n < 2 * length:
        return F(0)
    return F((n - length) ** 2 * (2 * length - n) ** 2, length ** 4)


def quotient_direct(a, s, h, length, squarefree=True):
    return sum(
        (mobius(v) ** 2 if squarefree else 1) * sample_weight(v, length)
        * exp2pi(F(-h * pow(a * v, -1, s), s))
        for v in range(length + 1, 2 * length)
        if math.gcd(v, a * s) == 1
    )


def quotient_square_expanded(a, s, h, length, tmax=None):
    limit = math.isqrt(2 * length)
    if tmax is not None:
        limit = min(limit, tmax)
    return sum(
        mobius(t) * sample_weight(t * t * w, length)
        * exp2pi(F(-h * pow(a * t * t * w, -1, s), s))
        for t in range(1, limit + 1) if math.gcd(t, a * s) == 1
        for w in range(1, (2 * length - 1) // (t * t) + 1)
        if math.gcd(w, a * s) == 1
    )


def quotient_discrete_completed(a, s, h, length):
    total = 0j
    for t in range(1, math.isqrt(2 * length) + 1):
        if math.gcd(t, a * s) != 1 or not mobius(t):
            continue
        for b in divisors(a):
            if not mobius(b):
                continue
            scale = t * t * b
            max_n = (2 * length - 1) // scale
            # Exact discrete transform: its samples already contain the
            # quotient length E/(t^2 b), so the outside factor here is 1/s.
            transform = [
                sum(sample_weight(scale * n, length) * exp2pi(F(-m * n, s))
                    for n in range(1, max_n + 1))
                for m in range(s)
            ]
            total += F(mobius(t) * mobius(b), s) * sum(
                transform[m]
                * kloosterman(s, pow(a * scale, -1, s) * m, -h)
                for m in range(s)
            )
    return total


class JointOuterModeChecks(unittest.TestCase):
    def test_all_integer_type_identity(self):
        for n in range(2, 101):
            for cutoff in range(1, min(n, 12)):
                self.assertEqual(-sum(term[3] for term in type_terms(n, cutoff)),
                                 mobius(n))

    def test_prime_cube_support_witness(self):
        terms = type_terms(8, 2)
        self.assertEqual(terms, [(1, 1, 8, 1), (1, 2, 4, -1),
                                 (2, 1, 4, -1), (2, 2, 2, 1)])
        self.assertEqual(-sum(term[3] for term in terms), 0)
        restricted = -sum(value for a, b, v, value in terms if mobius(a * b))
        self.assertEqual(restricted, 1)
        self.assertNotEqual(restricted, mobius(8))

    def test_squarefree_support_factorization(self):
        for a in range(1, 25):
            for b in range(1, 25):
                if not mobius(a) * mobius(b):
                    continue
                for v in range(1, 25):
                    expected = (int(math.gcd(a, b) == 1) * mobius(v) ** 2
                                * int(math.gcd(v, a * b) == 1))
                    self.assertEqual(mobius(a * b * v) ** 2, expected)

    def test_original_squarefree_type_support_restores_mu(self):
        for n in range(2, 101):
            for cutoff in range(1, min(n, 8)):
                restricted = -sum(
                    value * int(math.gcd(a, b) == 1) * mobius(v) ** 2
                    * int(math.gcd(v, a * b) == 1)
                    for a, b, v, value in type_terms(n, cutoff)
                )
                self.assertEqual(restricted, mobius(n))

    def test_single_mu_mode_regrouping_retains_q_smooth_frequencies(self):
        for q in (1, 2, 6, 35):
            for n in range(1, 101):
                coeff = sum(mobius(a) for a in divisors(n) if math.gcd(a, q) == 1)
                self.assertEqual(coeff, int(coprime_part(n, q) == 1))
        self.assertEqual(sum(mobius(a) for a in divisors(12)
                             if math.gcd(a, 6) == 1), 1)

    def test_two_mu_mode_regrouping(self):
        for q in (1, 2, 6, 35):
            for n in range(1, 101):
                coeff = sum(mu_square_convolution(a) for a in divisors(n)
                            if math.gcd(a, q) == 1)
                self.assertEqual(coeff, mobius(coprime_part(n, q)))

    def test_squarefree_outer_truncation_changes_frequency_coefficient(self):
        for n in range(1, 101):
            coeff = sum(mu_square_convolution(a) * mobius(a) ** 2
                        for a in divisors(n))
            self.assertEqual(coeff, (-1) ** len(primes(n)))
        self.assertEqual(mu_square_convolution(4), 1)
        self.assertEqual(sum(mu_square_convolution(a) for a in divisors(4)), 0)
        self.assertEqual(sum(mu_square_convolution(a) * mobius(a) ** 2
                             for a in divisors(4)), -1)

    def test_joint_frequency_reindexing_retains_a_dependent_weight(self):
        def weight(a, j):
            return F(a + 2 * j, a * j + 1)
        for q in (1, 6, 35):
            limit = 70
            original = sum(mu_square_convolution(a) * weight(a, j)
                           for a in range(1, limit + 1) if math.gcd(a, q) == 1
                           for j in range(1, limit // a + 1))
            reindexed = sum(
                sum(mu_square_convolution(a) * weight(a, n // a)
                    for a in divisors(n) if math.gcd(a, q) == 1)
                for n in range(1, limit + 1)
            )
            self.assertEqual(original, reindexed)

    def test_squarefree_quotient_discrete_completion(self):
        for a, s in ((2, 5), (4, 3), (3, 7), (10, 9), (7, 8)):
            for h in (0, 1, -2):
                for length in (8, 15):
                    with self.subTest(a=a, s=s, h=h, length=length):
                        direct = quotient_direct(a, s, h, length)
                        expanded = quotient_square_expanded(a, s, h, length)
                        completed = quotient_discrete_completed(a, s, h, length)
                        self.assertLess(abs(direct - expanded), 1e-12)
                        self.assertLess(abs(direct - completed), 1e-11)

    def test_squarefree_weight_cannot_be_dropped(self):
        # Positive h=0 fixture makes the discarded nonsquarefree integers
        # visible without possible phase cancellation.
        direct = quotient_direct(1, 5, 0, 8)
        unweighted = quotient_direct(1, 5, 0, 8, squarefree=False)
        self.assertGreater(abs(direct - unweighted), 0.01)

    def test_square_divisor_tail_without_divisor_cost(self):
        for length in (8, 15, 32):
            for a, s in ((1, 5), (6, 7), (35, 8)):
                full = quotient_direct(a, s, 1, length)
                for cutoff in range(1, math.isqrt(2 * length) + 2):
                    partial = quotient_square_expanded(a, s, 1, length, cutoff)
                    absolute_count = sum(
                        sum(length < t * t * w < 2 * length
                            for w in range(1, 2 * length))
                        for t in range(cutoff + 1, math.isqrt(2 * length) + 1)
                    )
                    self.assertLessEqual(absolute_count, F(2 * length, cutoff))
                    self.assertLessEqual(abs(full - partial), float(absolute_count) + 1e-12)
                    if cutoff >= math.isqrt(2 * length):
                        self.assertLess(abs(full - partial), 1e-12)

    def test_frequency_dilation_pays_for_its_jacobian(self):
        for length in (F(13), F(71, 2)):
            for s in (7, 19):
                for t in (1, 2, 5):
                    for b in (1, 3, 11):
                        jacobian = length / (t * t * b * s)
                        mode_scale = t * t * b * s / length
                        self.assertEqual(jacobian * mode_scale, 1)

    def test_zero_ramanujan_division_witness(self):
        self.assertEqual(ramanujan(4, 1), 0)
        self.assertLess(abs(kloosterman(3, 1, -1) - 2), 1e-12)
        self.assertLess(abs(kloosterman(12, 1, -4)), 1e-12)

    def test_discrete_full_zero_mode_cancellation(self):
        # Finite analogue of sum_k uhat(kH/s)=(s/H)sum_a u(as/H).
        # It checks the full-transform ordering, not the continuous proof.
        for period in (5, 7, 12):
            samples = [F(0)] + [F(n, period) for n in range(1, period)]
            transformed = [sum(samples[n] * exp2pi(F(-k * n, period))
                               for n in range(period)) for k in range(period)]
            self.assertLess(abs(sum(transformed)), 1e-11)
            self.assertGreater(abs(transformed[0]), 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
