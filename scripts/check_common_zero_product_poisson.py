#!/usr/bin/env python3
"""Finite guards for the smooth raw-Mobius common-zero row estimate.

Algebraic identities use exact cyclotomic arithmetic. Numerical norm checks
are small-modulus sanity checks, NOT proofs of analytic estimates, physical
packet coverage, prime-pair dispersion, or any zero-free theorem.
"""

import cmath
from fractions import Fraction as Rat
from itertools import product
from math import ceil, gcd, lcm, pi, sqrt
import unittest

from check_pre_cauchy_common_determinant import inv, mobius, root_normal_form


def units(modulus):
    return [n for n in range(modulus) if gcd(n, modulus) == 1]


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def prime_divisors(n):
    return [p for p in divisors(n) if p > 1
            and all(p % d for d in range(2, int(sqrt(p)) + 1))]


def is_supported_smooth(n, r):
    for p in prime_divisors(r):
        while n % p == 0:
            n //= p
    return n == 1


def ramanujan_prime(a, p):
    return p - 1 if a % p == 0 else -1


def common_terms(g, A, J, K, n):
    if gcd(n, g) != 1:
        return []
    return [(A * n * inv(a * b, g) + J * a + K * b, Rat(1))
            for a, b in product(units(g), repeat=2)]


def active_terms(q, j, k, c, n):
    # Deliberate zero extension; the unit formula must NOT be used at n=0.
    if gcd(n, q) != 1:
        return []
    return ([(j * a + k * c * n * inv(a, q), Rat(1)) for a in units(q)]
            + [(0, -Rat(ramanujan_prime(j, q) * ramanujan_prime(k, q), q - 1))])


def literal_terms(g, q, A, c, j, k, n):
    modulus = g * q
    if gcd(n, modulus) != 1:
        return []
    return [(j * a + k * b + q * A * n * inv(a * b, g),
             Rat(int((a * b - c * n) % q == 0)) - Rat(1, q - 1))
            for a, b in product(units(modulus), repeat=2)]


def factored_terms(g, q, A, c, j, k, n):
    gt = common_terms(g, A, j * inv(q, g), k * inv(q, g), n)
    pt = active_terms(q, j * inv(g, q), k * inv(g, q), c, n)
    return [(q * x + g * y, a * b) for x, a in gt for y, b in pt]


def complex_value(modulus, terms):
    return sum(float(coefficient) * cmath.exp(2j * pi * (exponent % modulus) / modulus)
               for exponent, coefficient in terms)


def discrete_logs(p):
    for generator in units(p):
        logs = {pow(generator, k, p): k for k in range(p - 1)}
        if len(logs) == p - 1:
            return logs
    raise AssertionError("prime unit group must be cyclic")


class ProductPoissonChecks(unittest.TestCase):
    def assertRootsEqual(self, modulus, left, right):
        self.assertEqual(root_normal_form(modulus, left), root_normal_form(modulus, right))

    def test_literal_crt_factorization_including_nonunits(self):
        for g, q in ((2, 3), (3, 5), (6, 5), (10, 3)):
            for j, k in product((0, 1, 2, q, g, g * q - 1), repeat=2):
                for n in (0, 1, 2, 3, 5, 7):
                    self.assertRootsEqual(g * q,
                                          literal_terms(g, q, g - 1, 2, j, k, n),
                                          factored_terms(g, q, g - 1, 2, j, k, n))

    def test_active_axes_vanish_exactly(self):
        for q in (3, 5, 7, 11):
            for k, c, n in product(range(q), units(q), range(q)):
                self.assertRootsEqual(q, active_terms(q, 0, k, c, n), [])
                self.assertRootsEqual(q, active_terms(q, k, 0, c, n), [])

    def test_nonunit_extension_cannot_use_unit_formula(self):
        for q in (3, 5, 7):
            self.assertEqual(active_terms(q, 1, 1, 1, 0), [])
            wrong_formula = [(a, Rat(1)) for a in units(q)] + [(0, -Rat(1, q - 1))]
            self.assertNotEqual(root_normal_form(q, wrong_formula), (0,))
            self.assertEqual(common_terms(q, 1, 1, 1, 0), [])

    def test_active_zero_mean(self):
        for q in (3, 5, 7):
            for j, k, c in product(units(q), repeat=3):
                terms = [term for n in range(q) for term in active_terms(q, j, k, c, n)]
                self.assertRootsEqual(q, terms, [])

    def test_active_additive_transform_exact(self):
        for q in (3, 5, 7):
            for j, k, c, t in product(units(q), repeat=4):
                direct = [(exponent - t * n, coefficient) for n in range(q)
                          for exponent, coefficient in active_terms(q, j, k, c, n)]
                expected = [(j * k * c * inv(t, q), Rat(q)), (0, Rat(q, q - 1))]
                self.assertRootsEqual(q, direct, expected)

    def test_common_hyper_kloosterman_substitution(self):
        for ell in (2, 3, 5, 7):
            for A, J, K, n in product(units(ell), repeat=4):
                hyper = [(x + y + A * J * K * n * inv(x * y, ell), Rat(1))
                         for x, y in product(units(ell), repeat=2)]
                self.assertRootsEqual(ell, common_terms(ell, A, J, K, n), hyper)

    def test_common_degenerate_frequencies(self):
        for ell in (2, 3, 5, 7, 11):
            for A, J, n in product(units(ell), repeat=3):
                self.assertRootsEqual(ell, common_terms(ell, A, J, 0, n), [(0, 1)])
                self.assertRootsEqual(ell, common_terms(ell, A, 0, J, n), [(0, 1)])
                self.assertRootsEqual(ell, common_terms(ell, A, 0, 0, n), [(0, 1 - ell)])

    def test_common_additive_transform_exact(self):
        for ell in (2, 3, 5, 7):
            for A, J, K, t in product(units(ell), units(ell), units(ell), range(ell)):
                direct = [(exponent - t * n, coefficient / ell) for n in range(ell)
                          for exponent, coefficient in common_terms(ell, A, J, K, n)]
                expected = [(0, -Rat(1, ell))]
                if t:
                    expected += [(A * z + J * K * inv(t * z, ell), Rat(1))
                                 for z in units(ell)]
                self.assertRootsEqual(ell, direct, expected)

    def test_common_mellin_is_three_gauss_sums_exact(self):
        for ell in (2, 3, 5, 7):
            logs, modulus = discrete_logs(ell), lcm(ell, ell - 1)
            fexp, cexp = modulus // ell, modulus // (ell - 1)
            for A, J, K, character in product(units(ell), (1, ell - 1),
                                             (1, ell - 1), range(ell - 1)):
                direct = [(fexp * exponent + cexp * character * logs[n], coefficient)
                          for n in units(ell)
                          for exponent, coefficient in common_terms(ell, A, J, K, n)]
                gauss = [(fexp * (x + y + z) + cexp * character
                          * (logs[x] + logs[y] + logs[z] - logs[A * J * K % ell]), Rat(1))
                         for x, y, z in product(units(ell), repeat=3)]
                self.assertRootsEqual(modulus, direct, gauss)

    def test_active_mellin_is_two_gauss_sums_exact(self):
        for q in (3, 5, 7):
            logs, modulus = discrete_logs(q), lcm(q, q - 1)
            fexp, cexp = modulus // q, modulus // (q - 1)
            for j, k, c, character in product((1, q - 1), (1, q - 1),
                                             (1, q - 1), range(1, q - 1)):
                direct = [(fexp * exponent + cexp * character * logs[n], coefficient)
                          for n in units(q)
                          for exponent, coefficient in active_terms(q, j, k, c, n)]
                gauss = [(fexp * (x + y) + cexp * character
                          * (logs[x] + logs[y] - logs[j * k * c % q]), Rat(1))
                         for x, y in product(units(q), repeat=2)]
                self.assertRootsEqual(modulus, direct, gauss)

    def test_common_squarefree_crt_twists(self):
        for g in (6, 10, 15):
            for J, K, n in product((0, 1, 2, 3), (0, 1, 3, 5), units(g)):
                assembled = [(0, Rat(1))]
                for ell in prime_divisors(g):
                    factor, twist = g // ell, inv(g // ell, ell)
                    local = common_terms(ell, twist, J * twist, K * twist, n)
                    assembled = [(a + factor * b, wa * wb)
                                 for a, wa in assembled for b, wb in local]
                self.assertRootsEqual(g, common_terms(g, 1, J, K, n), assembled)

    def test_small_composite_additive_norm_sanity(self):
        for g, q in ((2, 3), (6, 5), (10, 3)):
            modulus = g * q
            for j, k in product((1, 2, g), repeat=2):
                if j % q == 0 or k % q == 0:
                    continue
                values = [complex_value(modulus, factored_terms(g, q, 1, 1, j, k, n))
                          / (g * sqrt(q)) for n in range(modulus)]
                self.assertLess(abs(sum(values)), 1e-9)
                bound = 2 * 3 ** len(prime_divisors(g)) * sqrt(modulus * gcd(g, gcd(j, k)))
                for t in range(modulus):
                    transformed = sum(value * cmath.exp(-2j * pi * t * n / modulus)
                                      for n, value in enumerate(values))
                    self.assertLessEqual(abs(transformed), bound + 1e-9)

    def test_two_cutoff_mobius_identity(self):
        for n in range(2, 180):
            for U in (1, 2, 3, 5, 12):
                if U >= n:
                    continue
                small, large = 0, 0
                for b in divisors(n):
                    for c in divisors(n // b):
                        value = mobius(b) * mobius(c)
                        small += value * int(b <= U and c <= U)
                        large += value * int(b > U and c > U)
                self.assertEqual(mobius(n), -small + large)

    def test_type_two_regrouping_retains_exact_cutoffs(self):
        for modulus, N in ((6, 6), (15, 22), (30, 71)):
            U = ceil(Rat(2 * N, modulus))
            for n in range(N + 1, 2 * N):
                literal = sum(mobius(b) * mobius(c)
                              for b in divisors(n) if b > U
                              for c in divisors(n // b) if c > U)
                grouped = sum(mobius(b) * sum(mobius(c) for c in divisors(n // b) if c > U)
                              for b in divisors(n) if U < b < modulus and U < n // b < modulus)
                self.assertEqual(literal, grouped)

    def test_injective_type_two_integer_labels(self):
        for modulus in range(6, 40):
            for N in range(modulus, int(modulus ** (4 / 3)) + 1):
                U = ceil(Rat(2 * N, modulus))
                self.assertLess(U, N)
                for b in range(U + 1, 2 * N // (U + 1) + 1):
                    for s in range(U + 1, (2 * N - 1) // b + 1):
                        self.assertLess(b, modulus)
                        self.assertLess(s, modulus)

    def test_truncation_cannot_be_replaced_by_whole_dyadic_interval(self):
        modulus = 15
        # Enlarging [8,15) to [8,16] introduces another label for 1 mod 15.
        self.assertEqual(1 % modulus, 16 % modulus)
        self.assertNotIn(16, range(8, modulus))

    def test_type_one_exponent_range_exact(self):
        for qexp, nexp in ((Rat(5, 2), Rat(3)), (Rat(3), Rat(4)), (Rat(3), Rat(3))):
            self.assertLessEqual(2 * nexp - 3 * qexp / 2, (nexp + qexp) / 2)
        self.assertGreater(2 * Rat(41, 10) - Rat(9, 2), (Rat(41, 10) + 3) / 2)

    def test_coprime_mobius_convolution_keeps_prime_powers(self):
        for r in (1, 2, 6, 10, 30):
            for n in range(1, 200):
                actual = sum(mobius(n // s) for s in divisors(n) if is_supported_smooth(s, r))
                self.assertEqual(actual, mobius(n) * int(gcd(n, r) == 1))
        wrong_squarefree_only = sum(mobius(4 // s) for s in (1, 2))
        self.assertEqual(wrong_squarefree_only, -1)
        self.assertEqual(mobius(4) * int(gcd(4, 2) == 1), 0)

    def test_large_smooth_tail_and_integer_endpoint_cost(self):
        for N, modulus, r in ((30, 15, 6), (71, 30, 10), (150, 60, 30)):
            cut = Rat(N, modulus)
            for s in range(1, 2 * N):
                self.assertLessEqual(Rat(N, s) + 1, Rat(3 * N, s))
                if s > cut:
                    self.assertLessEqual(Rat(N, s) ** 2, Rat(N * modulus, s))
            finite = sum(s ** -0.5 for s in range(1, 2 * N) if is_supported_smooth(s, r))
            euler = 1.0
            for p in prime_divisors(r):
                euler /= 1 - p ** -0.5
            self.assertLessEqual(finite, euler)

    def test_fixed_h_delta_unit_rescaling(self):
        g, q, A, c, ah, bd = 6, 5, 5, 2, 7, 11
        modulus = g * q
        for h, delta, n in product(units(modulus), repeat=3):
            lhs_phase = A * n * inv(ah * h * bd * delta, g) % g
            rhs_phase = (A * inv(ah * bd, g)) * n * inv(h * delta, g) % g
            self.assertEqual(lhs_phase, rhs_phase)
            self.assertEqual((ah * bd * h * delta - c * n) % q == 0,
                             (h * delta - c * inv(ah * bd, q) * n) % q == 0)

    def test_gcd_mode_divisor_reassembly_sanity(self):
        for g in (2, 6, 30, 210):
            for j, k in product(range(-8, 9), repeat=2):
                if j == 0 or k == 0:
                    continue
                d = gcd(g, gcd(j, k))
                expansion = 0.0
                for divisor in divisors(d):
                    coefficient = 1.0
                    for ell in prime_divisors(divisor):
                        coefficient *= sqrt(ell) - 1
                    expansion += coefficient
                self.assertAlmostEqual(expansion, sqrt(d), places=12)

    def test_nonzero_modes_have_no_constant_count_term(self):
        for a in (0.01, 0.1, 1, 10):
            for d in (1, 2, 5):
                # Decreasing-function integral: sum_{j!=0,d|j}(1+|j|/a)^-2 <= 2a/d.
                finite = sum(2 * (1 + d * n / a) ** -2 for n in range(1, 1000))
                self.assertLessEqual(finite, 2 * a / d)
        self.assertGreater(1, 2 * 0.01)  # j=0 would destroy that bound.

    def test_extreme_model_local_gain_not_prime_occupancy_gain(self):
        gexp, qexp, nexp = Rat(1), Rat(3, 2), Rat(3)
        Qexp = gexp + qexp
        improved = gexp + qexp / 2 + (nexp + Qexp) / 2
        trivial = gexp + qexp / 2 + nexp
        self.assertEqual(improved, Rat(9, 2))
        self.assertEqual(trivial, Rat(19, 4))
        self.assertEqual(trivial - improved, Rat(1, 4))
        self.assertEqual(qexp / 2, Rat(3, 4))
        self.assertGreater(qexp / 2, trivial - improved)

    def test_two_occupancy_bounds_have_different_normalizations(self):
        multiplicities = [2, 3, 2, 3]
        values = [1 + 2j, -3j, 4 - 1j, 2]
        left = sum(count * abs(value) ** 2 for count, value in zip(multiplicities, values))
        energy_bound = max(multiplicities) * sum(abs(value) ** 2 for value in values)
        pointwise_bound = sum(multiplicities) * max(abs(value) ** 2 for value in values)
        self.assertLessEqual(left, energy_bound)
        self.assertLessEqual(left, pointwise_bound)
        self.assertNotEqual(energy_bound, pointwise_bound)

    def test_active_gram_is_exact_scaled_mean_zero_projection(self):
        for q in (3, 5, 7):
            for j, k, a, b in product((1, q - 1), (1, q - 1), units(q), units(q)):
                direct = [(x - y, cx * cy / q) for c in units(q)
                          for x, cx in active_terms(q, j, k, c, a)
                          for y, cy in active_terms(q, j, k, c, b)]
                expected = Rat(q) * (int(a == b) - Rat(1, q - 1))
                self.assertRootsEqual(q, direct, [(0, expected)])

    def test_centered_residue_energy_and_signed_offdiagonal_exact(self):
        for q in (3, 5, 7):
            coefficients = {n: Rat(mobius(n) * (2 * n - 7), 11)
                            for n in range(12, 30) if gcd(n, q) == 1}
            classes = {a: sum(value for n, value in coefficients.items() if n % q == a)
                       for a in units(q)}
            mean = sum(classes.values()) / (q - 1)
            variance = sum((value - mean) ** 2 for value in classes.values())
            diagonal = (1 - Rat(1, q - 1)) * sum(value ** 2 for value in coefficients.values())
            offdiagonal = sum(x * y * (int((n - m) % q == 0) - Rat(1, q - 1))
                              for n, x in coefficients.items() for m, y in coefficients.items()
                              if n != m)
            self.assertEqual(variance, diagonal + offdiagonal)
            rows = {c: [(phase, value * weight) for n, value in coefficients.items()
                        for phase, weight in active_terms(q, 1, 2, c, n)] for c in units(q)}
            energy_terms = [(x - y, wx * wy / q) for row in rows.values()
                            for x, wx in row for y, wy in row]
            self.assertRootsEqual(q, energy_terms, [(0, q * variance)])


if __name__ == "__main__":
    unittest.main(verbosity=2)
