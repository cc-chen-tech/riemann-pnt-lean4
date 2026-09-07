#!/usr/bin/env python3
"""Exact finite guards for signed gcd overlap and smooth-mode bookkeeping.

Finite mode sums are checks of the stated analytic majorant, not a proof
of its infinite version. No test asserts physical coverage or zeta bounds.
"""

from collections import defaultdict
from fractions import Fraction as Rat
from itertools import product
from math import gcd
import unittest

from check_pre_cauchy_common_determinant import inv, mobius, root_normal_form
from check_common_zero_product_poisson import divisors, units
from check_all_common_frequencies_prime_average import phi


def overlaps(d):
    """Signed inclusion-exclusion labels, not mutually exclusive events."""
    for a in divisors(d):
        for b in divisors(d // a):
            e = d // (a * b)
            if gcd(a, b) == gcd(a, e) == gcd(b, e) == 1:
                yield a, b, e


def overlap_mask(d, h, delta):
    return sum(mobius(a) * mobius(b) for a, b, e in overlaps(d)
               if h % (a * e) == 0 and delta % (b * e) == 0)


def mode_cost(g):
    return sum((Rat(phi(r), r * r) for r in divisors(g)), Rat(0))


def mode_factors(A, B, M):
    return min(Rat(1), A ** M) * min(Rat(1), B ** M)


def energy_exponent(gamma, sigma):
    return gamma + sigma + max(Rat(3), gamma + 2 * sigma) + 3


def pair_exponent(gamma, eta_l, eta_s, delta_l, delta_s, k_l, k_s):
    sl = 3 - eta_l - delta_l - gamma - k_l
    ss = 3 - eta_s - delta_s - gamma - k_s
    return (eta_l + eta_s + gamma
            + (energy_exponent(gamma, sl) + energy_exponent(gamma, ss) + sl - ss) / 2)


class GcdOverlapChecks(unittest.TestCase):
    def test_squarefree_signed_overlap_all_small_integers(self):
        checks = 0
        for d in range(1, 43):
            if not mobius(d):
                continue
            for h, delta in product(range(-8, 9), repeat=2):
                self.assertEqual(overlap_mask(d, h, delta), mobius(d) * int(h * delta % d == 0))
                checks += 1
        self.assertGreater(checks, 6000)

    def test_prime_overlap_is_not_disjoint_or_positive(self):
        p = 5
        terms = [mobius(a) * mobius(b) for a, b, e in overlaps(p)
                 if p % (a * e) == 0 and p % (b * e) == 0]
        self.assertEqual(sorted(terms), [-1, -1, 1])
        self.assertEqual(sum(terms), -1)
        self.assertNotEqual(sum(abs(x) for x in terms), abs(sum(terms)))

    def test_squarefree_hypothesis_is_needed(self):
        self.assertEqual(overlap_mask(4, 4, 1), mobius(4))
        self.assertEqual(overlap_mask(4, 4, 4), 1)
        self.assertNotEqual(overlap_mask(4, 4, 4), mobius(4))

    def test_true_gcd_condition_with_reduced_unit_mask(self):
        for d, q in ((1, 15), (6, 35), (10, 21), (15, 14)):
            for h, delta in product(range(-6, 7), repeat=2):
                self.assertEqual(gcd(abs(h * delta), d * q) == d,
                                 h * delta % d == 0 and gcd(h * delta, q) == 1)

    def test_overlap_quotient_and_two_scaled_lengths(self):
        for d in (1, 6, 10, 30):
            for a, b, e in overlaps(d):
                for u, w in product((-3, 1, 4), repeat=2):
                    h, delta = a * e * u, b * e * w
                    self.assertEqual(Rat(h * delta, d), e * u * w)
                H, L = Rat(13), Rat(17)
                self.assertEqual(H / (a * e) * L / (b * e), H * L / (d * e))

    def test_residual_variables_need_not_be_units_at_d(self):
        # This valid a=2,b=e=1 term has u divisible by d.
        d, q, a, b, e, u, w = 2, 15, 2, 1, 1, 2, 1
        h, delta = a * e * u, b * e * w
        self.assertEqual(gcd(h * delta, d * q), d)
        self.assertNotEqual(gcd(u * w, d), 1)

    def test_original_n_gcd_mask_is_not_redundant(self):
        d, q, h, delta, n = 2, 15, 2, 1, 2
        self.assertEqual(gcd(h * delta, q), 1)
        self.assertEqual(gcd(n, q), 1)
        self.assertNotEqual(gcd(n, d * q), 1)

    def test_common_phase_speed_and_row_label_rescale_exact(self):
        for d, g, c, k in ((6, 5, 7, 11), (10, 3, 7, 1)):
            for a, b, e in overlaps(d):
                for rh, rd in product(divisors(k), repeat=2):
                    multiplier = e * rh * rd
                    self.assertEqual(gcd(multiplier, g * c), 1)
                    self.assertEqual(len({nu * multiplier % g for nu in range(g)}), g)
                    for u, w, n in product(units(g * c), repeat=3):
                        # Restrict an otherwise large finite Cartesian product.
                        if u > 4 or w > 4 or n > 4:
                            continue
                        t = u * w * inv(n, g)
                        self.assertEqual(inv(multiplier * t, g), inv(multiplier, g) * inv(t, g) % g)
                        x = multiplier * u * w * inv(n, c) % c
                        self.assertEqual(x * inv(multiplier, c) % c, u * w * inv(n, c) % c)

    def test_finite_weighted_physical_row_reassembly_exact(self):
        for d, g, c, k in ((3, 5, 7, 2), (6, 5, 7, 11), (10, 3, 7, 1)):
            q = g * c * k
            original, expanded = defaultdict(list), defaultdict(list)
            for h, delta, n in product(range(1, 19), range(1, 16), range(1, 11)):
                if h * delta % d or gcd(h * delta, q) != 1 or gcd(n, d * q) != 1:
                    continue
                m = h * delta // d
                weight = mobius(d) * mobius(n) * (h - 2 * delta)
                x, t = m * inv(n, c) % c, m * inv(n, g) % g
                for nu in range(g):
                    original[nu, x].append((inv(t, g) + 2 * nu * t, Rat(weight)))
            for a, b, e in overlaps(d):
                for rh, rd in product(divisors(k), repeat=2):
                    for u, w, n in product(range(1, 18 // (a * e * rh) + 1),
                                           range(1, 15 // (b * e * rd) + 1), range(1, 11)):
                        if gcd(u * w * n, g * c) != 1 or gcd(n, d * k) != 1:
                            continue
                        h, delta = a * e * rh * u, b * e * rd * w
                        multiplier = e * rh * rd
                        weight = mobius(a) * mobius(b) * mobius(rh) * mobius(rd) * mobius(n) * (h - 2 * delta)
                        x = multiplier * u * w * inv(n, c) % c
                        t = multiplier * u * w * inv(n, g) % g
                        for nu in range(g):
                            expanded[nu, x].append((inv(t, g) + 2 * nu * t, Rat(weight)))
            self.assertTrue(original)
            for key in set(original) | set(expanded):
                self.assertEqual(root_normal_form(g, original[key]), root_normal_form(g, expanded[key]))

    def test_induced_divisors_preserve_product_lower_bound(self):
        for d, k in ((6, 35), (10, 21)):
            for a, b, e in overlaps(d):
                for rh, rd in product(divisors(k), repeat=2):
                    H, L = Rat(101), Rat(107)
                    direct = H / (a * e * rh) * L / (b * e * rd)
                    self.assertEqual(direct, H * L / (d * e * rh * rd))
                    self.assertGreaterEqual(direct, H * L / (d * e * k * k))

    def test_overlap_atom_count_is_three_to_omega(self):
        for d, omega in ((1, 0), (2, 1), (6, 2), (30, 3), (210, 4)):
            self.assertEqual(len(list(overlaps(d))), 3 ** omega)

    def test_gcd_mode_divisor_decomposition_exact(self):
        for g in (6, 10, 15, 30):
            for j, ell in product(range(-4, 5), repeat=2):
                self.assertEqual(gcd(g, gcd(j, ell)),
                                 sum(phi(r) for r in divisors(g) if j % r == ell % r == 0))

    def test_one_dimensional_mode_majorant_finite_exact(self):
        for x, J in product((Rat(1, 4), Rat(1), Rat(3, 2), Rat(4)), (2, 3, 5)):
            finite = 2 * sum(((1 + Rat(n) / x) ** (-J) for n in range(1, 31)), Rat(0))
            bound = Rat(2 * J, J - 1) * x * min(Rat(1), x ** (J - 1))
            self.assertLessEqual(finite, bound)

    def test_enhanced_two_dimensional_mode_majorant_finite_exact(self):
        for g, A, B, M in product((2, 6, 15), (Rat(1, 3), Rat(2)),
                                 (Rat(1, 4), Rat(3)), (0, 1, 2)):
            J = M + 2
            finite = sum((gcd(g, gcd(j, ell)) * (1 + Rat(abs(j)) / A) ** (-J)
                          * (1 + Rat(abs(ell)) / B) ** (-J)
                          for j in range(-8, 9) if j
                          for ell in range(-8, 9) if ell), Rat(0))
            bound = Rat(2 * J, J - 1) ** 2 * A * B * mode_cost(g) * mode_factors(A, B, M)
            self.assertLessEqual(finite, bound)

    def test_separate_mode_gains_are_stronger_than_product_gain(self):
        for A, B, M in product((Rat(1, 8), Rat(1), Rat(8)),
                               (Rat(1, 8), Rat(1), Rat(8)), (0, 1, 3)):
            self.assertLessEqual(mode_factors(A, B, M), min(Rat(1), (A * B) ** M))
        self.assertLess(mode_factors(Rat(1, 8), Rat(8), 2), 1)

    def test_directional_exponents_cancel_inactive_k(self):
        for aa, ab, xi, k, delta, upsilon in product(
                (Rat(0), Rat(1, 3)), (Rat(0), Rat(1, 4)), (Rat(0), Rat(3, 2)),
                (Rat(0), Rat(1, 5)), (Rat(0), Rat(1, 4)), (Rat(0), Rat(1, 2))):
            eta = aa + ab + xi
            Q = 3 - eta - delta - k
            h_effective = 3 - upsilon - aa - xi - k
            l_effective = 2 + upsilon - ab - xi - k
            x, y = ab + delta - upsilon, aa + delta + upsilon - 1
            self.assertEqual(h_effective - Q, x)
            self.assertEqual(l_effective - Q, y)
            self.assertEqual(x + y, -1 + eta - xi + 2 * delta)

    def test_remaining_collar_and_product_condition(self):
        rho = Rat(1, 20)
        for aa, ab, xi, delta, upsilon in product(
                (Rat(0), Rat(1, 4), Rat(3, 4)), (Rat(0), Rat(1, 4), Rat(3, 4)),
                (Rat(0), Rat(1), Rat(2)), (Rat(0), Rat(1, 4)), (Rat(0), Rat(1, 2))):
            x, y = ab + delta - upsilon, aa + delta + upsilon - 1
            self.assertGreaterEqual(max(x, 0) + max(y, 0), max(x + y, 0))
            if max(x, y) <= rho:
                eta = aa + ab + xi
                self.assertGreaterEqual(xi, eta + 2 * delta - 1 - 2 * rho)

    def test_full_overlap_can_still_have_one_direction_gain(self):
        aa = ab = upsilon = Rat(0)
        delta = Rat(1, 4)
        x, y = ab + delta - upsilon, aa + delta + upsilon - 1
        self.assertLess(x + y, 0)
        self.assertGreater(x, 0)

    def test_piecewise_genuine_gcd_pair_budget_exact(self):
        counts = defaultdict(int)
        for gamma, eta_l, eta_s, dl, ds, kl, ks in product(
                (Rat(0), Rat(1, 2), Rat(1)), (Rat(0), Rat(1), Rat(2)),
                (Rat(0), Rat(1), Rat(2)), (Rat(0), Rat(1, 2)),
                (Rat(0), Rat(1, 2)), (Rat(0), Rat(1, 4)), (Rat(0), Rat(1, 4))):
            sl, ss = 3 - eta_l - dl - gamma - kl, 3 - eta_s - ds - gamma - ks
            if sl < ss or ss < 0:
                continue
            B = pair_exponent(gamma, eta_l, eta_s, dl, ds, kl, ks)
            if gamma + 2 * ss >= 3:
                self.assertEqual(B, 12 - eta_l - 2 * dl - ds - 2 * kl - ks)
                self.assertLessEqual(B, 12)
                counts['both_trace'] += 1
            elif gamma + 2 * sl <= 3:
                self.assertEqual(B, 12 - dl - kl - ds - ks - ss)
                self.assertLessEqual(B, 12)
                counts['both_length'] += 1
            else:
                self.assertEqual(B, Rat(21, 2) - eta_l + eta_s + gamma / 2 - 2 * dl - 2 * kl)
                if B > 12:
                    self.assertGreater(eta_s, Rat(3, 2) + eta_l - gamma / 2 + 2 * dl + 2 * kl)
                    self.assertGreater(eta_s, 1)
                counts['mixed'] += 1
        self.assertTrue(all(counts[k] > 20 for k in ('both_trace', 'both_length', 'mixed')))

    def test_uncontrolled_overlap_budget_witness_is_not_removed(self):
        gamma, eta_l, eta_s = Rat(1), Rat(0), Rat(19, 10)
        self.assertEqual(pair_exponent(gamma, eta_l, eta_s, 0, 0, 0, 0), Rat(129, 10))
        h_effective = l_effective = Rat(5, 2) - eta_s
        Q = 3 - eta_s
        self.assertEqual((h_effective, l_effective, Q), (Rat(3, 5), Rat(3, 5), Rat(11, 10)))
        self.assertLess(h_effective, Q)
        self.assertLess(l_effective, Q)


if __name__ == '__main__':
    unittest.main()
