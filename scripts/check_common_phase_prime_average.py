#!/usr/bin/env python3
"""Finite normalization checks for the common-coefficient prime average.

Exact root-of-unity identities are tested in cyclotomic quotient rings.
Finite floating norm checks are sanity checks, not proofs of the analytic
large sieve, uniform smoothness, physical coverage, or zero-free statements.
"""

from fractions import Fraction as Rat
from itertools import product
from math import ceil, gcd, sqrt
import unittest

from check_pre_cauchy_common_determinant import inv, mobius, root_normal_form
from check_common_zero_product_poisson import (
    active_terms, common_terms, complex_value, prime_divisors, units,
)


def primes_between(R):
    return [q for q in range(R + 1, 2 * R + 1)
            if all(q % p for p in range(2, int(sqrt(q)) + 1))]


def nondegenerate_modulus(g, j, k):
    modulus = 1
    for ell in prime_divisors(g):
        if (j * k) % ell:
            modulus *= ell
    return modulus


def degenerate_factor(g, j, k):
    result = Rat(1)
    for ell in prime_divisors(g):
        zeros = int(j % ell == 0) + int(k % ell == 0)
        if zeros == 1:
            result /= ell
        elif zeros == 2:
            result *= -Rat(ell - 1, ell)
    return result


def common_local_gram(ell, n, m):
    return ell * int(n % ell == m % ell) - Rat(ell * ell + ell + 1, ell * ell)


def prefix_blocks(size, stop):
    """Disjoint aligned dyadic intervals partitioning range(stop)."""
    if not 0 <= stop <= size or size & (size - 1):
        raise ValueError("power-of-two padded size and legal prefix required")
    blocks, left, length = [], 0, size
    while length:
        if stop - left >= length:
            blocks.append((left, left + length))
            left += length
        length //= 2
    return blocks


def primitive_profile(q, coefficients, C, g, j, k):
    if (j * k) % q == 0:
        return {c: 0j for c in units(q)}
    result = {}
    for c in units(q):
        value = 0j
        for n, coefficient in coefficients.items():
            L = complex_value(g, common_terms(g, C, j * inv(q, g), k * inv(q, g), n)) / g
            p = complex_value(q, active_terms(q, j * inv(g, q), k * inv(g, q), c, n)) / sqrt(q)
            value += coefficient * L * p
        result[c] = value
    return result


class PrimeAverageChecks(unittest.TestCase):
    def assertRootsEqual(self, modulus, left, right):
        self.assertEqual(root_normal_form(modulus, left), root_normal_form(modulus, right))

    def test_effective_modulus_is_not_three_way_gcd(self):
        self.assertEqual(nondegenerate_modulus(30, 2, 3), 5)
        self.assertEqual(gcd(30, gcd(2, 3)), 1)
        self.assertEqual(nondegenerate_modulus(30, 6, 5), 1)
        self.assertEqual(nondegenerate_modulus(30, 1, 1), 30)

    def test_degenerate_constants_and_empty_product(self):
        self.assertEqual(degenerate_factor(30, 2, 3), Rat(1, 6))
        self.assertEqual(degenerate_factor(30, 6, 5), Rat(1, 30))
        self.assertEqual(degenerate_factor(6, 6, 6), Rat(1, 3))
        for g in (2, 6, 30):
            for j, k in product(range(1, 12), repeat=2):
                self.assertLessEqual(abs(degenerate_factor(g, j, k)), 1)

    def test_common_parameter_gram_exact_at_primes(self):
        for ell in (2, 3, 5, 7):
            for J, K, n, m in product((1, ell - 1), (1, ell - 1), units(ell), units(ell)):
                direct = [(x - y, cx * cy / (ell * ell)) for A in units(ell)
                          for x, cx in common_terms(ell, A, J, K, n)
                          for y, cy in common_terms(ell, A, J, K, m)]
                self.assertRootsEqual(ell, direct, [(0, common_local_gram(ell, n, m))])

    def test_common_parameter_gram_exact_squarefree_crt(self):
        for g in (6, 10, 15):
            for n, m in product(units(g), repeat=2):
                direct = [(x - y, cx * cy / (g * g)) for A in units(g)
                          for x, cx in common_terms(g, A, 1, 1, n)
                          for y, cy in common_terms(g, A, 1, 1, m)]
                gram = Rat(1)
                for ell in prime_divisors(g):
                    gram *= common_local_gram(ell, n, m)
                self.assertRootsEqual(g, direct, [(0, gram)])

    def test_gauss_bessel_zero_class_difference_exact(self):
        for q in (3, 5, 7, 11):
            for shift in (-2, 0, 3):
                B = {r: Rat((r + shift) ** 2 - 5 * r, 7) for r in range(q)}
                total = sum(B[r] for r in units(q))
                additive = q * sum(x * x for x in B.values()) - sum(B.values()) ** 2
                multiplicative = q * sum(B[r] ** 2 for r in units(q)) - Rat(q, q - 1) * total ** 2
                difference = ((q - 1) * B[0] - total) ** 2 / (q - 1)
                self.assertEqual(additive - multiplicative, difference)
                self.assertGreaterEqual(difference, 0)

    def test_additive_side_must_retain_q_divisible_indices(self):
        q = 5
        coefficients = {q: Rat(3), 1: Rat(2), 2: Rat(-1)}
        full = [sum(value for n, value in coefficients.items() if n % q == r) for r in range(q)]
        masked = [0] + full[1:]
        energy = lambda v: q * sum(x * x for x in v) - sum(v) ** 2
        self.assertNotEqual(energy(full), energy(masked))

    def test_progression_additive_transform_permutation_exact(self):
        for g0, q in ((1, 5), (2, 5), (6, 7)):
            for r in range(g0):
                coefficients = {m: Rat(m * m - 2, 3) for m in range(-2, 7)}
                for v in units(q):
                    original = [(v * (r + g0 * m), value) for m, value in coefficients.items()]
                    transformed = [(v * r + (g0 * v % q) * m, value)
                                   for m, value in coefficients.items()]
                    self.assertRootsEqual(q, original, transformed)
                self.assertEqual(sorted(g0 * v % q for v in units(q)), units(q))

    def test_fixed_g_unit_mask_is_common_after_progression_split(self):
        g, g0, coefficients = 30, 5, {n: mobius(n) for n in range(21, 62)}
        original = sum(value ** 2 for n, value in coefficients.items() if gcd(n, g) == 1)
        partitioned = sum(value ** 2 for r in units(g0) for n, value in coefficients.items()
                          if n % g0 == r and gcd(n, g) == 1)
        self.assertEqual(original, partitioned)

    def test_progression_interval_rounding_and_absorption(self):
        for N, g0 in product(range(1, 18), range(1, 15)):
            for r in range(g0):
                count = sum(n % g0 == r for n in range(N + 1, 2 * N + 1))
                self.assertLessEqual(count, ceil(Rat(N, g0)))
            for R in (2, 5):
                self.assertLessEqual(g0 * ceil(Rat(N, g0)) + 4 * g0 * R * R,
                                     N + 5 * g0 * R * R)

    def test_additive_farey_circular_spacing(self):
        for R in (2, 4, 7, 11):
            points = [Rat(v, q) for q in primes_between(R) for v in units(q)]
            self.assertEqual(len(points), len(set(points)))
            for i, x in enumerate(points):
                for y in points[i + 1:]:
                    gap = abs(x - y)
                    self.assertGreaterEqual(min(gap, 1 - gap), Rat(1, 4 * R * R))

    def test_arbitrary_phase_selection_bounded_by_unit_completion_sanity(self):
        for g, R, j, k in ((6, 5, 1, 1), (6, 5, 2, 1), (6, 5, 6, 6), (5, 4, 1, 2)):
            g0 = nondegenerate_modulus(g, j, k)
            coefficients = {n: mobius(n) * ((n % 5) - 2) for n in range(20, 41)}
            for index, q in enumerate(primes_between(R)):
                if gcd(q, g * j * k) != 1:
                    continue
                C = units(g)[(index + q) % len(units(g))]
                rows = primitive_profile(q, coefficients, C, g, j, k)
                energy = sum(abs(x) ** 2 for x in rows.values())
                upper = 0.0
                for r in units(g0):
                    B = [sum(value for n, value in coefficients.items()
                             if gcd(n, g) == 1 and n % g0 == r and n % q == t)
                         for t in range(q)]
                    upper += q * sum(x * x for x in B) - sum(B) ** 2
                upper *= g0 * float(degenerate_factor(g, j, k) ** 2)
                self.assertLessEqual(energy, upper + 1e-8)

    def test_fixed_mode_large_sieve_finite_sanity(self):
        for g, R, N, j, k in ((6, 5, 40, 1, 1), (6, 7, 50, 2, 3), (5, 6, 45, 1, 2)):
            coefficients = {n: mobius(n) for n in range(N + 1, 2 * N + 1)}
            lhs = 0.0
            for q in primes_between(R):
                if gcd(q, g * j * k) != 1:
                    continue
                C = units(g)[q % len(units(g))]
                lhs += sum(abs(x) ** 2 for x in primitive_profile(q, coefficients, C, g, j, k).values())
            g0 = nondegenerate_modulus(g, j, k)
            upper = float(degenerate_factor(g, j, k) ** 2) * (N + 5 * g0 * R * R)
            upper *= sum(x * x for n, x in coefficients.items() if gcd(n, g) == 1)
            self.assertLessEqual(lhs, upper + 1e-8)

    def test_prefix_dyadic_blocks_cover_once_at_each_scale(self):
        for size in (1, 2, 4, 8, 32):
            for stop in range(size + 1):
                blocks = prefix_blocks(size, stop)
                self.assertEqual([n for left, right in blocks for n in range(left, right)], list(range(stop)))
                lengths = [right - left for left, right in blocks]
                self.assertEqual(len(lengths), len(set(lengths)))
                self.assertTrue(all(left % (right - left) == 0 for left, right in blocks))

    def test_prefix_maximal_square_majorant(self):
        values = [complex((i * i) % 7 - 3, i % 3 - 1) for i in range(16)]
        all_blocks = [(left, left + length) for length in (1, 2, 4, 8, 16)
                      for left in range(0, 16, length)]
        majorant = 5 * sum(abs(sum(values[left:right])) ** 2 for left, right in all_blocks)
        self.assertLessEqual(max(abs(sum(values[:stop])) ** 2 for stop in range(17)), majorant)

    def test_discrete_abel_bound_for_row_dependent_weights(self):
        for offset in (0, 2, 5):
            terms = [complex((i * i) % 7 - 3, i % 3 - 1) for i in range(12)]
            weights = [complex(i + offset, offset - i * i) / 144 for i in range(12)]
            partials = [sum(terms[:i + 1]) for i in range(12)]
            abel = weights[-1] * partials[-1]
            abel += sum((weights[i] - weights[i + 1]) * partials[i] for i in range(11))
            direct = sum(x * w for x, w in zip(terms, weights))
            self.assertAlmostEqual(abs(abel - direct), 0, places=12)
            variation = abs(weights[-1]) + sum(abs(weights[i] - weights[i + 1]) for i in range(11))
            self.assertLessEqual(abs(direct), variation * max(abs(x) for x in partials) + 1e-12)

    def test_poisson_prefactor_all_mode_reassembly(self):
        for g, R, H, L in ((6, 7, 13, 29), (10, 11, 1, 10000)):
            # Squared prefactor times squared natural mode count is exactly g²R.
            prefactor_squared = Rat(H * H * L * L, g * g * R**3)
            mode_count_squared = Rat(g**4 * R**4, H * H * L * L)
            self.assertEqual(prefactor_squared * mode_count_squared, g * g * R)

    def test_prime_pair_sampling_and_occupancy(self):
        P, R, D = 30, 7, 11
        longs = [p for p in primes_between(P) if p != D]
        shorts = [q for q in primes_between(R) if q != D]
        self.assertGreater(P, 2 * R)
        for p in longs:
            residues = [D * inv(q, p) % p for q in shorts]
            self.assertEqual(len(residues), len(set(residues)))
        for q in shorts:
            residues = [-D * inv(p, q) % q for p in longs]
            self.assertLessEqual(max(residues.count(a) for a in units(q)), 1 + Rat(P, R))

    def test_pair_cauchy_uses_actual_cross_residues(self):
        P, R, D = 30, 7, 11
        longs = [p for p in primes_between(P) if p != D]
        shorts = [q for q in primes_between(R) if q != D]
        A = {p: {a: complex(a % 3 - 1, a % 5 - 2) for a in units(p)} for p in longs}
        B = {q: {a: complex(a % 5 - 2, a % 3 - 1) for a in units(q)} for q in shorts}
        total = sum(A[p][D * inv(q, p) % p] * B[q][-D * inv(p, q) % q].conjugate()
                    for p in longs for q in shorts)
        EL = sum(abs(x) ** 2 for row in A.values() for x in row.values())
        ES = sum(abs(x) ** 2 for row in B.values() for x in row.values())
        self.assertLessEqual(abs(total) ** 2, float(1 + Rat(P, R)) * EL * ES)

    def test_top_energy_and_pair_exponents_exact(self):
        g, P, R, N = Rat(1), Rat(2), Rat(3, 2), Rat(3)
        energy = lambda Q: 2 * g + Q + max(N, g + 2 * Q) + N
        old_energy = lambda Q: 2 * g + 2 * Q + max(N, Q) + N
        self.assertEqual(energy(P), 12)
        self.assertEqual(energy(R), Rat(21, 2))
        self.assertEqual(old_energy(P), 12)
        self.assertEqual(old_energy(R), 11)
        pair = (P - R + energy(P) + energy(R)) / 2
        old_pair = (P - R + old_energy(P) + old_energy(R)) / 2
        self.assertEqual(pair, Rat(23, 2))
        self.assertEqual(old_pair, Rat(47, 4))
        self.assertEqual(old_pair - pair, Rat(1, 4))

    def test_arbitrary_level_dependent_coefficients_are_not_common(self):
        # A simple rank-two coefficient matrix cannot be silently one sequence.
        rows = [[Rat(1), Rat(0)], [Rat(0), Rat(1)]]
        self.assertNotEqual(rows[0][0] * rows[1][1] - rows[0][1] * rows[1][0], 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
