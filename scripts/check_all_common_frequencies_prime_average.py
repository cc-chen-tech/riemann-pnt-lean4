#!/usr/bin/env python3
"""Finite guards for the all-common-frequency prime-average theorem.

Root identities use exact cyclotomic arithmetic. Floating norm checks are
small-instance sanity checks, not proofs of the large sieve, smooth Poisson
reassembly, physical coverage, or a zero-free statement.
"""

from fractions import Fraction as Rat
from itertools import product
from math import gcd, lcm, sqrt
import unittest

from check_pre_cauchy_common_determinant import inv, mobius, root_normal_form
from check_common_zero_product_poisson import (
    active_terms, common_terms, complex_value, discrete_logs, divisors,
    prime_divisors, units,
)
from check_common_phase_prime_average import primes_between


def phi(n):
    return len(units(n))


def local_characters(g):
    """All unit characters as exponents of a common primitive root."""
    primes = prime_divisors(g)
    order = lcm(*(p - 1 for p in primes))
    logs = {p: discrete_logs(p) for p in primes}
    for indices in product(*(range(p - 1) for p in primes)):
        yield order, {
            n: sum(k * logs[p][n % p] * (order // (p - 1))
                   for p, k in zip(primes, indices)) % order
            for n in units(g)
        }


def kernel_terms(g, J, K, n, phase, amplitude=None):
    if gcd(n, g) != 1:
        return []
    amplitude = amplitude or {t: Rat(1) for t in units(g)}
    result = []
    for u, v in product(units(g), repeat=2):
        t = u * v * inv(n, g) % g
        result.append((phase[t] + J * u + K * v, amplitude[t] / g))
    return result


def mode_cost(g):
    return sum((Rat(phi(d), d * d) for d in divisors(g)), Rat(0))


def arbitrary_phase(g):
    # At g=15 this fails the multiplicative CRT rectangle identity.
    return {t: int(t == 1) + (t * t if g % 5 else 0) for t in units(g)}


class AllCommonFrequencyChecks(unittest.TestCase):
    def assertRootsEqual(self, modulus, left, right):
        self.assertEqual(root_normal_form(modulus, left),
                         root_normal_form(modulus, right))

    def test_character_enumeration_and_orthogonality_exact(self):
        for g in (2, 3, 6, 10, 15, 30):
            characters = list(local_characters(g))
            self.assertEqual(len(characters), phi(g))
            order = characters[0][0]
            for n, m in product(units(g), repeat=2):
                terms = [(chi[n] - chi[m], Rat(1)) for _, chi in characters]
                self.assertRootsEqual(order, terms, [(0, phi(g) * int(n == m))])

    def test_mellin_identity_for_nonfactorable_input_exact(self):
        for g in (2, 3, 6, 10, 15, 30):
            phase = arbitrary_phase(g)
            amplitude = {t: Rat((t % 5) - 2, 3) for t in units(g)}
            for J, K in ((0, 0), (0, 1), (1, 0), (1, 1), (2, 3)):
                for order, chi in local_characters(g):
                    modulus = lcm(g, order)
                    sg, sc = modulus // g, modulus // order
                    left = [(sg * x - sc * chi[n], c) for n in units(g)
                            for x, c in kernel_terms(g, J, K, n, phase, amplitude)]
                    right = [(sg * (J * u + K * v + phase[t])
                              + sc * (-chi[u] - chi[v] + chi[t]), amplitude[t] / g)
                             for u, v, t in product(units(g), repeat=3)]
                    self.assertRootsEqual(modulus, left, right)

    def test_chosen_input_really_is_not_crt_factorable(self):
        g, phase = 15, arbitrary_phase(15)
        # 1,7,11,2 have CRT coordinates (1,1),(1,2),(2,1),(2,2).
        self.assertNotEqual((phase[1] + phase[2] - phase[7] - phase[11]) % g, 0)

    def test_local_gauss_squared_norms_exact(self):
        for ell in (2, 3, 5, 7):
            for order, chi in local_characters(ell):
                principal = all(x == 0 for x in chi.values())
                modulus = lcm(ell, order)
                for J in range(ell):
                    terms = [(J * u * (modulus // ell) - chi[u] * (modulus // order), Rat(1))
                             for u in units(ell)]
                    squared = [(x - y, a * b) for x, a in terms for y, b in terms]
                    expected = ((ell - 1) ** 2 if principal else 0) if J == 0 else (1 if principal else ell)
                    self.assertRootsEqual(modulus, squared, [(0, expected)])

    def test_local_multiplier_cost_all_degeneracies(self):
        for ell in (2, 3, 5, 7):
            for J, K in product(range(ell), repeat=2):
                d = gcd(ell, gcd(J, K))
                principal_squared = Rat(((ell - 1) ** 2 if J == 0 else 1)
                                        * ((ell - 1) ** 2 if K == 0 else 1), ell * ell)
                self.assertLessEqual(principal_squared, d * d)
                if ell > 2:
                    nonprincipal_squared = int(J != 0 and K != 0)
                    self.assertLessEqual(nonprincipal_squared, d * d)

    def test_common_nonunit_zero_extension(self):
        for g in (6, 10, 15):
            for n in range(g):
                if gcd(n, g) != 1:
                    self.assertEqual(kernel_terms(g, 1, 1, n, arbitrary_phase(g)), [])

    def test_arbitrary_input_operator_bound_sanity(self):
        for g in (2, 3, 6, 10, 15, 30):
            amplitude = {t: Rat((t % 5) - 2, 3) for t in units(g)}
            for J, K in ((0, 0), (0, 1), (1, 0), (1, 1), (2, 3), (g, g)):
                norms = [complex_value(g, kernel_terms(g, J, K, n, arbitrary_phase(g), amplitude))
                         for n in units(g)]
                bound = gcd(g, gcd(J, K)) ** 2 * sum(a * a for a in amplitude.values())
                self.assertLessEqual(sum(abs(z) ** 2 for z in norms), float(bound) + 1e-8)

    def test_fully_degenerate_constant_kernel_exact(self):
        for ell in (2, 3, 5, 7):
            phase = arbitrary_phase(ell)
            for n in units(ell):
                self.assertRootsEqual(ell, kernel_terms(ell, 0, 0, n, phase),
                                      [(phase[t], Rat(ell - 1, ell)) for t in units(ell)])
        # Nonzero B may accidentally equal the B=0 constant; no "only if".
        phase = {t: inv(t, 3) + t for t in units(3)}
        self.assertRootsEqual(3, kernel_terms(3, 0, 0, 1, phase), [(0, -Rat(2, 3))])

    def test_uniform_g_only_energy_would_be_false(self):
        ell = 7
        phase = {t: 0 for t in units(ell)}
        terms = [term for n in units(ell)
                 for x, a in kernel_terms(ell, 0, 0, n, phase)
                 for y, b in kernel_terms(ell, 0, 0, n, phase)
                 for term in [(x - y, a * b)]]
        expected = Rat((ell - 1) ** 5, ell * ell)
        self.assertRootsEqual(ell, terms, [(0, expected)])
        self.assertGreater(expected, ell)

    def test_old_zero_frequency_is_exact_specialization(self):
        for g in (2, 3, 6, 10):
            A = g - 1
            phase = {t: A * inv(t, g) for t in units(g)}
            for J, K, n in product((0, 1, 2), (0, 1, 3), units(g)):
                self.assertRootsEqual(g, kernel_terms(g, J, K, n, phase),
                                      [(x, a / g) for x, a in common_terms(g, A, J, K, n)])

    def test_physical_phase_all_nu_keeps_both_terms(self):
        for g, q in ((5, 7), (6, 5), (10, 3)):
            C, iq = g - 1, inv(q, g)
            for nu, m, n in product(range(g), units(g), units(g)):
                t = m * inv(n, g) % g
                expanded = -C * iq * n * inv(m, g) + nu * iq * m * inv(n, g)
                ratio = -C * iq * inv(t, g) + nu * iq * t
                self.assertEqual((expanded - ratio) % g, 0)

    def test_literal_product_poisson_factorization_all_phases_exact(self):
        for g, q in ((2, 3), (3, 5), (6, 5), (10, 3)):
            phase = arbitrary_phase(g)
            modulus = g * q
            for j, k, n in product((0, 1, g, q), (0, 1, g), (0, 1, 2, q)):
                literal = []
                if gcd(n, modulus) == 1:
                    literal = [(j * u + k * v + q * phase[u * v * inv(n, g) % g],
                                Rat(int((u * v - n) % q == 0)) - Rat(1, q - 1))
                               for u, v in product(units(modulus), repeat=2)]
                left = kernel_terms(g, j * inv(q, g), k * inv(q, g), n, phase)
                right = active_terms(q, j * inv(g, q), k * inv(g, q), 1, n)
                factored = [(q * x + g * y, g * a * b) for x, a in left for y, b in right]
                self.assertRootsEqual(modulus, literal, factored)

    def test_axes_and_active_divisibility_vanish_exactly(self):
        for q in (3, 5, 7):
            for c, n, j in product(units(q), range(q), range(q)):
                self.assertRootsEqual(q, active_terms(q, j, q, c, n), [])
                self.assertRootsEqual(q, active_terms(q, q, j, c, n), [])

    def test_three_way_gcd_is_invariant_under_crt_unit_scaling(self):
        for g, q in ((6, 5), (10, 7), (15, 2), (30, 7)):
            for j, k in product(range(1, 12), repeat=2):
                self.assertEqual(gcd(g, gcd(j, k)), gcd(g, gcd(j * inv(q, g), k * inv(q, g))))

    def test_gcd_divisor_identity_exact(self):
        for g in (2, 6, 10, 15, 30, 210):
            for j, k in product(range(-8, 9), repeat=2):
                d = gcd(g, gcd(j, k))
                self.assertEqual(d, sum(phi(r) for r in divisors(g) if j % r == k % r == 0))

    def test_mode_cost_euler_product_exact(self):
        for g in (2, 3, 6, 10, 15, 30, 210):
            expected = Rat(1)
            for ell in prime_divisors(g):
                expected *= 1 + Rat(1, ell) - Rat(1, ell * ell)
            self.assertEqual(mode_cost(g), expected)

    def test_complete_divisor_weighted_mode_bound_sanity(self):
        J = 3
        for g, a, b in ((6, Rat(1, 3), Rat(1, 5)), (30, Rat(3), Rat(5)), (210, Rat(2), Rat(1, 2))):
            partial = sum(float(gcd(g, gcd(j, k))) * (1 + abs(j) / float(a)) ** -J
                          * (1 + abs(k) / float(b)) ** -J
                          for j in range(-40, 41) if j
                          for k in range(-40, 41) if k)
            bound = Rat(4) * a * b * mode_cost(g) / (J - 1) ** 2
            self.assertLessEqual(partial, float(bound) + 1e-10)

    def test_fixed_mode_prime_average_arbitrary_phase_sanity(self):
        for g, R, N, j, k in ((6, 5, 40, 1, 1), (6, 5, 40, 6, 6), (10, 7, 70, 2, 5)):
            coefficients = {n: mobius(n) * ((n % 5) - 2) for n in range(N + 1, 2 * N + 1)}
            energy = 0.0
            for q in primes_between(R):
                if gcd(q, g * j * k) != 1:
                    continue
                phase = {t: int(t == q % g) + q * t * t for t in units(g)}
                residue = {r: 0j for r in units(q)}
                for n, a in coefficients.items():
                    if gcd(n, g * q) == 1:
                        L = complex_value(g, kernel_terms(g, j * inv(q, g), k * inv(q, g), n, phase))
                        residue[n % q] += a * L
                mean = sum(residue.values()) / (q - 1)
                energy += q * sum(abs(z - mean) ** 2 for z in residue.values())
            bound = gcd(g, gcd(j, k)) ** 2 * (N + 5 * g * R * R) * sum(a * a for a in coefficients.values())
            self.assertLessEqual(energy, bound + 1e-8)

    def test_poisson_normalization_and_full_frequency_average(self):
        g, R, H, L = 30, 7, 11, 13
        # Square removes the q^(3/2) and sqrt(R) radicals.
        self.assertEqual(Rat(H * L, g) ** 2 / R ** 3
                         * Rat(g * g * R * R, H * L) ** 2, g * g * R)
        for g in (2, 6, 15, 30):
            weights = [complex_value(g, [(nu * 7, Rat(1))]) for nu in range(g)]
            self.assertLessEqual(abs(sum(weights) / g), 1 + 1e-12)
            self.assertEqual(sum((Rat(1, g) for _ in range(g)), Rat(0)), 1)

    def test_extreme_exponents_do_not_add_a_second_saving(self):
        gamma, P, R, N, norm2 = Rat(1), Rat(2), Rat(3, 2), Rat(3), Rat(3)
        EL = 2 * gamma + P + max(N, gamma + 2 * P) + norm2
        ES = 2 * gamma + R + max(N, gamma + 2 * R) + norm2
        pair = (EL + ES + P - R) / 2
        self.assertEqual((EL, ES, pair), (12, Rat(21, 2), Rat(23, 2)))
        self.assertEqual(Rat(47, 4) - pair, Rat(1, 4))


if __name__ == "__main__":
    unittest.main()
