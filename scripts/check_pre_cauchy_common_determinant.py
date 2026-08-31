#!/usr/bin/env python3
"""Finite normalization guards, not a long-prime estimate or zero-free proof.

Root-of-unity identities are compared exactly over Q[X]/Phi_g(X).
The ordinary Weil inequality is only numerically sanity-checked at small primes.
"""

import cmath
from collections import Counter
from fractions import Fraction as Q
from functools import cache
from itertools import product
from math import gcd, pi, sqrt
import unittest


def trim(poly):
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def divrem_monic(poly, divisor):
    poly = trim(list(poly))
    quotient = [Q(0)] * max(1, len(poly) - len(divisor) + 1)
    while len(poly) >= len(divisor) and poly != [0]:
        shift = len(poly) - len(divisor)
        coefficient = poly[-1]
        quotient[shift] += coefficient
        for j, value in enumerate(divisor):
            poly[j + shift] -= coefficient * value
        trim(poly)
    return trim(quotient), trim(poly)


@cache
def cyclotomic(n):
    poly = [-1] + [0] * (n - 1) + [1]
    for d in range(1, n):
        if n % d == 0:
            poly, remainder = divrem_monic(poly, cyclotomic(d))
            assert remainder == [0]
    return tuple(poly)


def root_normal_form(g, terms):
    poly = [Q(0)] * g
    for exponent, coefficient in terms:
        poly[exponent % g] += coefficient
    return tuple(divrem_monic(poly, cyclotomic(g))[1])


def inv(value, modulus):
    return pow(value, -1, modulus)


def mobius(n):
    result, divisor = 1, 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            result *= -1
            n //= divisor
            if n % divisor == 0:
                return 0
        divisor += 1
    return -result if n > 1 else result


def residual(p, q, D, m, n, u, v):
    return p * n * u - q * m * v - D * n * v


def phase(g, p, q, C1, C2, m, n, u, v):
    return (-C1 * n * inv(p * m, g)
            + C2 * v * inv(q * u, g)) % g


def frequency(g, p, q, D, m, n, u, v):
    return (D * inv(p * q, g) + m * inv(p * n, g)
            - u * inv(q * v, g)) % g


def admissible(g, p, q, m, n, u, v):
    return gcd(m * n, g * p) == gcd(u * v, g * q) == 1


def incidences(p, q, D, m, n, u, v):
    return (int((q * m + D * n) % p == 0),
            int((p * u - D * v) % q == 0))


def ray_phase(g, P, D, x, y, z, C1=1, C2=1):
    q_class = (P * x - D * z) * inv(y, g) % g
    return (-C1 * z * inv(P * y, g)
            + C2 * z * inv(q_class * x, g)) % g


def omega(g, D, x, z):
    return [P for P in range(g) if gcd(P * (P * x - D * z), g) == 1]


class CommonDeterminantChecks(unittest.TestCase):
    def assertRootsEqual(self, g, left, right):
        self.assertEqual(root_normal_form(g, left), root_normal_form(g, right))

    def test_cyclotomic_normalization(self):
        self.assertEqual(cyclotomic(6), (1, -1, 1))
        self.assertEqual(cyclotomic(10), (1, -1, 1, -1, 1))
        for g in (2, 3, 5, 6, 10, 15, 30):
            for k in range(g):
                self.assertRootsEqual(g, [(nu * k, Q(1, g)) for nu in range(g)],
                                      [(0, int(k == 0))])

    def test_literal_crt_row_has_the_restored_phase(self):
        for g, p in ((5, 7), (6, 5), (10, 3)):
            for m, n, nu in product(range(1, 10), range(1, 10), range(g)):
                if gcd(m * n, g * p) != 1:
                    continue
                z = -m * inv(p * n, g) % g
                C = g - 1
                original = C * inv(p * p * z, g) - nu * z
                eliminated = -C * n * inv(p * m, g) + nu * m * inv(p * n, g)
                self.assertEqual((original - eliminated) % g, 0)

    def test_common_numerator_keeps_signs_and_all_densities(self):
        for g, p, q in ((5, 7, 3), (6, 5, 7), (10, 7, 3)):
            for D in (-5, -1, 1, 5):
                if gcd(D, p * q) != 1:
                    continue
                for m, n, u, v in product(range(1, 8), repeat=4):
                    if not admissible(g, p, q, m, n, u, v):
                        continue
                    R = residual(p, q, D, m, n, u, v)
                    self.assertEqual(frequency(g, p, q, D, m, n, u, v),
                                     -R * inv(p * q * n * v, g) % g)

    def test_four_term_centered_residual_reassembly(self):
        for g, p, q, D in ((5, 7, 3, 1), (6, 5, 7, -1), (10, 7, 3, 5)):
            original, assembled, zero, nonzero = [], [], [], []
            expanded = []
            for m, n, u, v in product(range(1, 9), repeat=4):
                if not admissible(g, p, q, m, n, u, v):
                    continue
                Ip, Iq = incidences(p, q, D, m, n, u, v)
                density = (Ip - Q(1, p - 1)) * (Iq - Q(1, q - 1))
                weight = (m - 2 * u) * mobius(n) * mobius(v)
                phi = phase(g, p, q, 1, g - 1, m, n, u, v)
                freq = frequency(g, p, q, D, m, n, u, v)
                original += [(phi + nu * freq, weight * density / g) for nu in range(g)]
                R = residual(p, q, D, m, n, u, v)
                if R % g != 0:
                    continue
                assembled.append((phi, weight * density))
                (zero if R == 0 else nonzero).append((phi, weight * density))
                for component in (Ip * Iq, -Q(Ip, q - 1), -Q(Iq, p - 1),
                                  Q(1, (p - 1) * (q - 1))):
                    expanded.append((phi, weight * component))
            self.assertRootsEqual(g, original, assembled)
            self.assertRootsEqual(g, assembled, zero + nonzero)
            self.assertRootsEqual(g, assembled, expanded)

    def test_quotient_and_determinant_identities(self):
        p, q = 7, 3
        nonzero_t = 0
        for D in (-5, -1, 1, 5):
            for m, n, u, v in product(range(1, 11), repeat=4):
                Ip, Iq = incidences(p, q, D, m, n, u, v)
                R = residual(p, q, D, m, n, u, v)
                if Ip:
                    r = (q * m + D * n) // p
                    self.assertEqual(R, p * (n * u - r * v))
                if Iq:
                    s = (p * u - D * v) // q
                    self.assertEqual(R, q * (n * s - m * v))
                if Ip and Iq:
                    self.assertEqual((n * u - r * v) % q, 0)
                    t = (n * u - r * v) // q
                    self.assertEqual(R, p * q * t)
                    self.assertEqual(r * s - m * u, D * t)
                    self.assertEqual(m * v - n * s, -p * t)
                    nonzero_t += t != 0
        self.assertGreater(nonzero_t, 0)

    def test_zero_layer_coherent_not_suppressed_by_g(self):
        g, p, q, D, m, n, u, v = 5, 7, 3, 1, 2, 1, 1, 1
        self.assertEqual(residual(p, q, D, m, n, u, v), 0)
        self.assertEqual(frequency(g, p, q, D, m, n, u, v), 0)
        self.assertEqual(phase(g, p, q, 1, 1, m, n, u, v), 3)
        coefficient = (1 - Q(1, 6)) * (1 - Q(1, 2))
        self.assertEqual(coefficient, Q(5, 12))
        self.assertRootsEqual(g, [(3, coefficient / g)] * g, [(3, coefficient)])
        self.assertNotEqual(root_normal_form(g, [(3, coefficient)]),
                            root_normal_form(g, [(3, coefficient / g)]))

    def test_cross_unit_hypothesis_is_necessary(self):
        # R=0, but both incidences fail on a legal original-unit tuple.
        g, p, q, D, m, n, u, v = 5, 7, 3, 1, 1, 3, 2, 7
        self.assertTrue(admissible(g, p, q, m, n, u, v))
        self.assertEqual(residual(p, q, D, m, n, u, v), 0)
        self.assertEqual(incidences(p, q, D, m, n, u, v), (0, 0))
        self.assertEqual(Q(1, (p - 1) * (q - 1)), Q(1, 12))

    def test_cross_unit_zero_layer_forces_both_incidences(self):
        for m, n, u, v in product(range(1, 12), repeat=4):
            if not admissible(5, 7, 3, m, n, u, v) or gcd(v, 7) != 1 or gcd(n, 3) != 1:
                continue
            if residual(7, 3, 1, m, n, u, v) == 0:
                self.assertEqual(incidences(7, 3, 1, m, n, u, v), (1, 1))

    def test_primitive_ray_is_unique_without_coprime_dilations(self):
        p, q, D = 7, 3, 1
        for a, b in product(range(1, 8), repeat=2):
            r, m, n, u, s, v = a, 2 * a, a, b, 2 * b, b
            self.assertEqual(p * r, q * m + D * n)
            self.assertEqual(q * s, p * u - D * v)
            self.assertEqual(residual(p, q, D, m, n, u, v), 0)
            self.assertEqual(gcd(gcd(r, m), n), a)
            self.assertEqual(gcd(gcd(u, s), v), b)
        self.assertGreater(gcd(2, 2), 1)

    def test_phase_is_independent_of_unit_dilations(self):
        for g in (5, 10, 11):
            for a, b in product(range(1, 13), repeat=2):
                m, n, u, v = 2 * a, a, b, b
                if not admissible(g, 7, 3, m, n, u, v):
                    continue
                self.assertEqual(phase(g, 7, 3, 1, g - 1, m, n, u, v),
                                 ray_phase(g, 7, 1, 1, 2, 1, 1, g - 1))

    def test_mobius_common_core_is_squared(self):
        for a, b, z in product(range(1, 20), repeat=3):
            actual = mobius(a * z) * mobius(b * z)
            expected = (mobius(z) ** 2 * mobius(a) * mobius(b)
                        * int(gcd(a, z) == gcd(b, z) == 1))
            self.assertEqual(actual, expected)

    def test_full_ray_weight_reassembly(self):
        g, p, q, D, limit = 5, 7, 3, 1, 16
        direct, reconstructed, cores = [], [], set()
        for m, n, u, v in product(range(1, limit + 1), repeat=4):
            if not admissible(g, p, q, m, n, u, v):
                continue
            if incidences(p, q, D, m, n, u, v) != (1, 1):
                continue
            if residual(p, q, D, m, n, u, v) != 0:
                continue
            r = (q * m + D * n) // p
            a = gcd(gcd(r, m), n)
            cores.add((r // a, m // a, n // a))
            weight = (m - 4) * (u - 2) * mobius(n) * mobius(v)
            direct.append((phase(g, p, q, 1, 2, m, n, u, v), weight))
        for x, y, z in cores:
            left = sum(mobius(a) * (a * y - 4)
                       for a in range(1, min(limit // y, limit // z) + 1)
                       if gcd(a, z) == 1 and gcd(a * a * y * z, g * p) == 1)
            right = sum(mobius(b) * (b * x - 2)
                        for b in range(1, min(limit // x, limit // z) + 1)
                        if gcd(b, z) == 1 and gcd(b * b * x * z, g * q) == 1)
            reconstructed.append((ray_phase(g, p, D, x, y, z, 1, 2),
                                  mobius(z) ** 2 * left * right))
        self.assertGreater(len(cores), 0)
        self.assertRootsEqual(g, direct, reconstructed)

    def test_kloosterman_change_of_variable_exact(self):
        for ell in (2, 3, 5, 7, 11):
            for a0, alpha, beta in product(range(1, ell), repeat=3):
                direct = [(alpha * inv(P, ell) + beta * inv(P - a0, ell), 1)
                          for P in range(1, ell) if P != a0]
                shift = (alpha - beta) * inv(a0, ell)
                transformed = [(shift + beta * inv(a0, ell) * U
                                - alpha * inv(a0, ell) * inv(U, ell), 1)
                               for U in range(1, ell)]
                transformed.append((0, -1))
                # Stronger than equality at roots: identical exponent histograms.
                lhs = Counter(exponent % ell for exponent, _ in direct)
                rhs = Counter()
                for exponent, coefficient in transformed:
                    rhs[exponent % ell] += coefficient
                self.assertEqual(+lhs, +rhs)
                self.assertRootsEqual(ell, direct, transformed)

    def test_pole_collision_exact_including_two(self):
        for ell in (2, 3, 5, 7, 11):
            for alpha, beta in product(range(1, ell), repeat=2):
                direct = [((alpha + beta) * inv(P, ell), 1) for P in range(1, ell)]
                expected = ell - 1 if (alpha + beta) % ell == 0 else -1
                self.assertRootsEqual(ell, direct, [(0, expected)])

    def test_physical_collision_condition(self):
        for ell in (3, 5, 7):
            for x, y, z, C1, C2 in product(range(1, ell), repeat=5):
                alpha = -C1 * z * inv(y, ell)
                beta = C2 * z * y * inv(x * x, ell)
                self.assertEqual((alpha + beta) % ell == 0,
                                 (C2 * y * y - C1 * x * x) % ell == 0)

    def test_crt_complete_sum_includes_twists_and_divisors_of_D(self):
        for g, primes in ((6, (2, 3)), (15, (3, 5)), (35, (5, 7))):
            for D in (1, 3, 5, 15, -1):
                x, y, z, C1, C2 = 1, g - 1, 1, 1, g - 1
                direct = [(ray_phase(g, P, D, x, y, z, C1, C2), 1)
                          for P in omega(g, D, x, z)]
                combined = [(0, 1)]
                for ell in primes:
                    factor = g // ell
                    twist = inv(factor, ell)
                    local = [(factor * twist * ray_phase(ell, P, D, x, y, z, C1, C2), 1)
                             for P in omega(ell, D, x, z)]
                    combined = [(a + b, ca * cb) for a, ca in combined for b, cb in local]
                self.assertRootsEqual(g, direct, combined)

    def test_weil_bound_only_small_finite_sanity(self):
        for ell in (3, 5, 7, 11, 13, 17):
            for alpha, beta in product(range(1, ell), repeat=2):
                value = sum(cmath.exp(2j * pi * ((alpha * inv(P, ell)
                           + beta * inv(P - 1, ell)) % ell) / ell)
                            for P in range(2, ell))
                self.assertLessEqual(abs(value), 2 * sqrt(ell) + 1 + 1e-10)

    def test_weighted_residue_mean_remainder_is_exact(self):
        g, D, x, y, z = 15, 1, 1, 2, 1
        classes = omega(g, D, x, z)
        weights = {P: Q(P * P - 3 * P, 7) for P in classes}
        average = sum(weights.values()) / len(classes)
        original = [(ray_phase(g, P, D, x, y, z), weights[P]) for P in classes]
        mean = [(ray_phase(g, P, D, x, y, z), average) for P in classes]
        remainder = [(ray_phase(g, P, D, x, y, z), weights[P] - average) for P in classes]
        self.assertRootsEqual(g, original, mean + remainder)
        self.assertEqual(sum(weights[P] - average for P in classes), 0)

    def test_arbitrary_weights_can_cancel_the_entire_phase(self):
        g, D, x, y, z = 11, 1, 1, 2, 1
        classes = omega(g, D, x, z)
        terms = [(ray_phase(g, P, D, x, y, z) - ray_phase(g, P, D, x, y, z), 1)
                 for P in classes]
        self.assertRootsEqual(g, terms, [(0, len(classes))])
        self.assertGreater(len(classes), 0)

    def test_empty_two_adic_support_is_retained(self):
        self.assertEqual(omega(2, 1, 1, 1), [])
        self.assertEqual(omega(6, 1, 1, 1), [])
        self.assertEqual(omega(2, 2, 1, 1), [1])

    def test_three_adic_singleton_not_claimed_oscillatory(self):
        self.assertEqual(omega(3, 1, 1, 1), [2])
        self.assertEqual(ray_phase(3, 2, 1, 1, 1, 1), 2)

    def test_support_separation_for_all_signed_box_corners(self):
        P, Qp, M, N, U, V, D0 = 1000, 10, 100, 10, 100, 10, 2
        lower = P * N * U - 8 * Qp * M * V - 4 * D0 * N * V
        self.assertGreater(lower, 0)
        for p, q, m, n, u, v, D in product(
                (P, 2 * P), (Qp, 2 * Qp), (-2 * M, -M, M, 2 * M),
                (N, 2 * N), (-2 * U, -U, U, 2 * U), (V, 2 * V), (-D0, D0)):
            self.assertGreaterEqual(abs(residual(p, q, D, m, n, u, v)), lower)

    def test_extreme_scale_gap_and_quotient_range_are_rational(self):
        for T in (100, 10000, 10**8):
            ratio = 1 - Q(8, int(sqrt(T))) - Q(4, T**3)
            self.assertGreater(ratio, Q(1, 8))
            upper_ratio = 8 + Q(8, int(sqrt(T))) + Q(4, T**3)
            self.assertLess(upper_ratio, 9)
            self.assertEqual(Q(1, 8) / 4, Q(1, 32))
            self.assertEqual(Q(1, 32) / 2, Q(1, 64))
        self.assertEqual(Q(10) - (2 + Q(3, 2)), Q(13, 2))
        self.assertEqual(Q(13, 2) - 1, Q(11, 2))

    def test_upper_support_alone_does_not_exclude_zero_layer(self):
        # p=7,q=3 is unbalanced but the relevant physical ratios compensate.
        p, q, D, m, n, u, v = 7, 3, 1, 2, 1, 1, 1
        self.assertEqual(residual(p, q, D, m, n, u, v), 0)
        self.assertLessEqual(u, 100)
        self.assertLess(u, 100)  # cannot invent the missing lower endpoint

    def test_fourier_zero_and_integer_zero_are_distinct(self):
        g, p, q, D, m, n, u, v = 5, 7, 3, 1, 1, 1, 1, 1
        R = residual(p, q, D, m, n, u, v)
        self.assertEqual(R, 3)
        self.assertNotEqual(R % g, 0)
        phi = phase(g, p, q, 1, 1, m, n, u, v)
        self.assertNotEqual(root_normal_form(g, [(phi, Q(1, g))]), (0,))
        freq = frequency(g, p, q, D, m, n, u, v)
        self.assertRootsEqual(g, [(phi + nu * freq, Q(1, g)) for nu in range(g)],
                              [(0, 0)])


if __name__ == "__main__":
    unittest.main(verbosity=2)
