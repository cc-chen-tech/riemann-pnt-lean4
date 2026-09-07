#!/usr/bin/env python3
"""Finite identities and rational budgets for joint g/conductor averaging.

These checks do not prove the analytic large sieve or physical packet
coverage. In particular, they do not assert a bound for zeta zeros.
"""

from collections import defaultdict
from fractions import Fraction as Rat
from itertools import product
from math import gcd, lcm
import unittest

from check_pre_cauchy_common_determinant import inv, mobius, root_normal_form
from check_common_zero_product_poisson import divisors, units
from check_all_common_frequencies_prime_average import phi
from check_common_frequency_parseval_conductor_average import characters, conductor, square_terms
from check_genuine_gcd_overlap_smooth_modes import pair_exponent


def primitive_chars(c):
    return [(o, chi) for o, chi in characters(c) if conductor(c, chi) == c]


def ratio_row(g, c):
    row = defaultdict(Rat)
    for h, delta, n in product(range(1, 6), range(1, 5), range(1, 10)):
        if gcd(h * delta * n, g * c) == 1:
            weight = Rat(h - 3, 2) * Rat(delta % 3 - 1) * Rat(mobius(n) * (n % 4 - 1), 3)
            row[h * delta * inv(n, g) % g, h * delta * inv(n, c) % c] += weight
    return row


def descended_character(g, c, cg, cc):
    og, chi_g = cg
    oc, chi_c = cc
    r = conductor(g, chi_g)
    b, q, order = g // r, r * c, lcm(og, oc)
    reduced = {}
    for n in units(g * c):
        phase = ((order // og) * chi_g[n % g] + (order // oc) * chi_c[n % c]) % order
        if n % q in reduced:
            assert reduced[n % q] == phase
        reduced[n % q] = phase
    return r, b, q, order, reduced


def energy_global(gamma, sigma):
    return gamma + sigma + max(Rat(3), 2 * gamma + 2 * sigma) + 3


def pair_global(gamma, eta_l, eta_s, dl, ds, kl, ks):
    sl, ss = 3 - eta_l - dl - gamma - kl, 3 - eta_s - ds - gamma - ks
    return eta_l + eta_s + (energy_global(gamma, sl) + energy_global(gamma, ss) + sl - ss) / 2


class GlobalConductorChecks(unittest.TestCase):
    def assertRootsEqual(self, modulus, left, right):
        self.assertEqual(root_normal_form(modulus, left), root_normal_form(modulus, right))

    def test_actual_frequency_average_equals_weighted_ratio_energy(self):
        for g, c in ((2, 5), (6, 5), (10, 3), (15, 4)):
            row = ratio_row(g, c)
            selected = primitive_chars(c)
            modulus = lcm(g, *(o for o, _ in selected))
            lhs, rhs = [], []
            for o, chi in selected:
                sc, sg = modulus // o, modulus // g
                for nu in range(g):
                    vector = [(sg * (inv(t, g) + nu * (g - 1) * t) - sc * chi[x],
                               weight * Rat(1 if t % 3 else 2, 3)) for (t, x), weight in row.items()]
                    lhs.extend((e, a / (g * phi(c))) for e, a in square_terms(modulus, vector))
                for t in units(g):
                    vector = [(-sc * chi[x], row[t, x]) for x in units(c)]
                    rhs.extend((e, a * Rat(1 if t % 3 else 2, 3) ** 2 / phi(c))
                               for e, a in square_terms(modulus, vector))
            self.assertRootsEqual(modulus, lhs, rhs)

    def test_full_ratio_multiplicative_parseval_exact(self):
        for g, c in ((2, 5), (6, 5), (10, 3), (15, 4)):
            row = ratio_row(g, c)
            chars_g, selected = list(characters(g)), primitive_chars(c)
            modulus = lcm(*(o for o, _ in chars_g + selected))
            lhs, rhs = [], []
            for oc, cc in selected:
                for t in units(g):
                    vector = [(-(modulus // oc) * cc[x], row[t, x]) for x in units(c)]
                    lhs.extend((e, a / phi(c)) for e, a in square_terms(modulus, vector))
                for og, cg in chars_g:
                    vector = [(-(modulus // og) * cg[t] - (modulus // oc) * cc[x], weight)
                              for (t, x), weight in row.items()]
                    rhs.extend((e, a / (phi(g) * phi(c))) for e, a in square_terms(modulus, vector))
            self.assertRootsEqual(modulus, lhs, rhs)

    def test_complex_projection_requires_correct_conjugation(self):
        # g=2,c=5,h=delta=1, a_1=1,a_3=i; select chi(2)=i only.
        order, chi = next((o, ch) for o, ch in primitive_chars(5) if ch[2] == 1)
        self.assertEqual(order, 4)
        projection_coefficient = [(0, Rat(1)), (1 - chi[inv(3, 5)], Rat(1))]
        correct_n_factor = [(0, Rat(1)), (1 + chi[3], Rat(1))]
        wrong_n_factor = [(0, Rat(1)), (1 - chi[3], Rat(1))]
        self.assertRootsEqual(4, projection_coefficient, correct_n_factor)
        self.assertRootsEqual(4, square_terms(4, correct_n_factor), [(0, 4)])
        self.assertRootsEqual(4, square_terms(4, wrong_n_factor), [])

    def test_tensor_character_has_product_primitive_conductor(self):
        for g, c in ((6, 5), (10, 3), (15, 4), (7, 9)):
            for cg, cc in product(characters(g), primitive_chars(c)):
                r, b, q, _, reduced = descended_character(g, c, cg, cc)
                self.assertEqual(g, r * b)
                self.assertEqual(gcd(b, q), 1)
                self.assertEqual(conductor(q, reduced), q)
                self.assertEqual(phi(g) * phi(c), phi(b) * phi(q))
                self.assertGreater(q, 1)

    def test_principal_common_character_still_has_nonprincipal_active(self):
        for g, c in ((6, 5), (10, 3)):
            cg = next(ch for ch in characters(g) if conductor(g, ch[1]) == 1)
            for cc in primitive_chars(c):
                r, b, q, _, reduced = descended_character(g, c, cg, cc)
                self.assertEqual((r, b, q), (1, g, c))
                self.assertEqual(conductor(q, reduced), c)

    def test_descent_preserves_all_nonunit_values(self):
        for g, c in ((6, 5), (10, 3)):
            for cg, cc in product(characters(g), primitive_chars(c)):
                _, b, q, order, reduced = descended_character(g, c, cg, cc)
                og, chig = cg
                oc, chic = cc
                for n in range(1, 2 * g * c + 1):
                    original = [] if gcd(n, g * c) != 1 else [(
                        (order // og) * chig[n % g] + (order // oc) * chic[n % c], Rat(1))]
                    descended = [] if gcd(n, b * q) != 1 else [(reduced[n % q], Rat(1))]
                    self.assertRootsEqual(order, original, descended)

    def test_smooth_mask_divisor_expansion_exact(self):
        for b in (2, 6, 10, 15):
            for h in range(-15, 16):
                self.assertEqual(sum(mobius(s) for s in divisors(b) if h % s == 0), int(gcd(h, b) == 1))

    def test_n_mask_cannot_be_dropped_in_common_conductor_descent(self):
        g, c, n = 6, 5, 2
        cg = next(ch for ch in characters(g) if conductor(g, ch[1]) == 1)
        for cc in primitive_chars(c):
            _, b, q, order, reduced = descended_character(g, c, cg, cc)
            self.assertEqual((b, q), (6, 5))
            self.assertEqual(gcd(n, q), 1)
            self.assertNotEqual(gcd(n, g * c), 1)
            unmasked = [(reduced[n % q], Rat(1))]
            self.assertRootsEqual(order, square_terms(order, unmasked), [(0, 1)])
            self.assertNotEqual(root_normal_form(order, unmasked), root_normal_form(order, []))

    def test_totient_normalization_matches_large_sieve(self):
        for g, c in ((6, 5), (10, 9), (15, 4), (30, 7)):
            for r in divisors(g):
                b, q = g // r, r * c
                self.assertEqual(Rat(q * q, phi(g) * phi(c)), Rat(q, phi(b)) * Rat(q, phi(q)))

    def test_factor_representation_multiplicity_is_divisor_bounded(self):
        for G, R, b in ((6, 5, 1), (10, 4, 2), (15, 7, 3)):
            counts = defaultdict(int)
            for g in range(G + 1, 2 * G + 1):
                if not mobius(g) or g % b:
                    continue
                r = g // b
                for c in range(R + 1, 2 * R + 1):
                    if gcd(g, c) == 1:
                        q = r * c
                        counts[q] += 1
                        self.assertLessEqual(q, Rat(4 * G * R, b))
            for q, count in counts.items():
                self.assertLessEqual(count, len(divisors(q)))

    def test_convergent_b_weight_euler_identity_exact(self):
        for primes in ((2, 3), (2, 3, 5), (3, 5, 7)):
            squarefree = [1]
            for p in primes:
                squarefree += [p * b for b in squarefree]
            direct = sum((Rat(len(divisors(b)) ** 4, b * phi(b)) for b in squarefree), Rat(0))
            euler = Rat(1)
            for p in primes:
                euler *= 1 + Rat(16, p * (p - 1))
            self.assertEqual(direct, euler)
            # log Euler factor <=16/(p(p-1)); these local majorants sum.
            self.assertLessEqual(sum((Rat(16, p * (p - 1)) for p in primes), Rat(0)), 16)

    def test_directional_gain_survives_inactive_common_divisors(self):
        for G, R, g, c in ((6, 5, 7, 6), (10, 4, 15, 7), (15, 7, 22, 9)):
            self.assertTrue(G < g <= 2 * G and R < c <= 2 * R)
            self.assertEqual(gcd(g, c), 1)
            for r in divisors(g):
                b, q = g // r, r * c
                for s in divisors(b):
                    self.assertLessEqual(q * s, g * c)
                    self.assertLessEqual(g * c, 4 * G * R)
                    for H in (Rat(1), Rat(100), Rat(1000)):
                        self.assertLessEqual(min(Rat(1), (q * s / H) ** 4),
                                             min(Rat(1), (4 * G * R / H) ** 4))

    def test_joint_energy_improves_only_length_term(self):
        for G, R, N in product((2, 5, 11), (3, 7), (10, 1000)):
            old = G * G * R * (N + G * R * R)
            new = G * R * (N + G * G * R * R)
            self.assertEqual(old - new, G * R * N * (G - 1))
            self.assertLessEqual(new, old)

    def test_pair_occupancy_algebra(self):
        for G, P, R in product((1, 3, 7), (5, 11), (2, 5)):
            self.assertEqual(G * P * G * R * (1 + Rat(R, P)) * (1 + Rat(P, R)), G * G * (P + R) ** 2)

    def test_piecewise_global_pair_exponents_exact(self):
        counts = defaultdict(int)
        for gamma, el, es, dl, ds, kl, ks in product(
                (Rat(0), Rat(1, 2), Rat(1)), (Rat(0), Rat(1), Rat(2)),
                (Rat(0), Rat(1), Rat(2)), (Rat(0), Rat(1, 2)),
                (Rat(0), Rat(1, 2)), (Rat(0), Rat(1, 4)), (Rat(0), Rat(1, 4))):
            sl, ss = 3 - el - dl - gamma - kl, 3 - es - ds - gamma - ks
            if sl < ss or ss < 0:
                continue
            result = pair_global(gamma, el, es, dl, ds, kl, ks)
            old = pair_exponent(gamma, el, es, dl, ds, kl, ks)
            self.assertLessEqual(result, old)
            if 2 * gamma + 2 * ss >= 3:
                self.assertEqual(result, 12 - el - 2 * dl - ds - 2 * kl - ks)
                self.assertLessEqual(result, 12)
                counts['trace'] += 1
            elif 2 * gamma + 2 * sl <= 3:
                self.assertEqual(result, 12 - gamma - dl - kl - ds - ks - ss)
                self.assertLessEqual(result, 12)
                counts['length'] += 1
            else:
                self.assertEqual(result, Rat(21, 2) - el + es - 2 * dl - 2 * kl)
                if result > 12:
                    self.assertGreater(es, Rat(3, 2) + el + 2 * dl + 2 * kl)
                counts['mixed'] += 1
        self.assertTrue(all(counts[k] > 10 for k in ('trace', 'length', 'mixed')))

    def test_unresolved_witness_improves_but_does_not_close(self):
        args = (Rat(1), Rat(0), Rat(19, 10), Rat(0), Rat(0), Rat(0), Rat(0))
        self.assertEqual(pair_exponent(*args), Rat(129, 10))
        self.assertEqual(pair_global(*args), Rat(62, 5))
        self.assertEqual((energy_global(1, Rat(2)), energy_global(1, Rat(1, 10))), (12, Rat(71, 10)))
        self.assertGreater(pair_global(*args), 12)

    def test_fixed_character_family_requires_N_term_exact(self):
        for m in (1, 2, 5, 11):
            N = 6 * m
            row, norm = defaultdict(int), 0
            for n in range(N + 1, 2 * N + 1):
                if gcd(n, 6) == 1:
                    weight = 1 if n % 3 == 1 else -1
                    row[inv(n, 3)] += weight
                    norm += weight * weight
            self.assertEqual(dict(row), {1: m, 2: -m})
            self.assertEqual(norm, 2 * m)
            self.assertEqual(sum(v * v for v in row.values()), 2 * m * m)
            # The common phase is (-1)^nu for both odd-n residue classes.
            averaged = Rat(sum(sum(((-1) ** nu * v) ** 2 for v in row.values()) for nu in range(2)), 2)
            self.assertEqual(averaged / norm, m)


if __name__ == '__main__':
    unittest.main()
