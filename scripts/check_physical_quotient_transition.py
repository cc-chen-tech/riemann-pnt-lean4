#!/usr/bin/env python3
"""Finite checks for physical quotient support and rational packets.

The sampled weights below are finite arithmetic fixtures, not C-infinity
approximations. These checks do not prove continuous Poisson, Schwartz
profile asymptotics, or the remaining signed Mobius estimate.
"""

from fractions import Fraction as F
import math
import unittest

from check_cubic_comb_mode_density import divisors, exp2pi, mobius
from check_joint_kernel_rational_flatness import (
    dft2, discrete_kernel, nonseparable_samples, rational_samples,
)
from check_joint_outer_mode_reassembly import type_terms


def interior_weight(x):
    left, right = F(5, 4), F(7, 4)
    return (x - left) ** 2 * (right - x) ** 2 if left < x < right else F(0)


def ratio_kernel(theta):
    return sum(F(1, 1 + abs(k) + abs(l)) * exp2pi(-theta * k * l)
               for k in range(-2, 3) for l in range(-2, 3))


def inverse_dft2(values):
    rows, cols = len(values), len(values[0])
    transformed = dft2([[x.conjugate() for x in row] for row in values])
    return [[x.conjugate() / (rows * cols) for x in row] for row in transformed]


def squarefree_restoration(a, v):
    return sum(mobius(t) * mobius(b)
               for t in range(1, math.isqrt(v) + 1) if math.gcd(t, a) == 1
               for b in divisors(a) if v % (t * t * b) == 0)


class PhysicalQuotientChecks(unittest.TestCase):
    def test_physical_frequency_support_and_large_c_vanish(self):
        r_scale = 20
        for c in (1, 3, 19, 40):
            for e in (1, 2, 7):
                for j in range(-45, 5):
                    weight = interior_weight(F(-j * c * e, r_scale))
                    if weight:
                        self.assertLess(j, 0)
                        self.assertLess(r_scale, -j * c * e)
                        self.assertLess(-j * c * e, 2 * r_scale)
                    if c * e >= 2 * r_scale:
                        self.assertEqual(weight, 0)

    def test_generic_near_zero_witness_is_outside_physical_support(self):
        height = 100
        d = height ** 3
        c = 16 * height ** 2 + 1
        self.assertEqual(math.gcd(c, d), 1)
        for j in (1, -1):
            self.assertEqual(interior_weight(F(-j * c, d)), 0)

    def test_all_cofactors_restore_coprimality_for_nonsquarefree_moduli(self):
        r_scale = 12
        for s in (4, 6, 8, 9, 12, 15):
            for c in (1, 5, 7):
                if math.gcd(c, s) != 1:
                    continue
                max_n = (2 * r_scale - 1) // c
                def weight(n):
                    return interior_weight(F(c * n, r_scale)) * ratio_kernel(F(-c * n, s))
                completed = sum(mobius(e) * weight(e * k)
                                for e in divisors(s)
                                for k in range(1, max_n // e + 1))
                original = sum(weight(n) for n in range(1, max_n + 1)
                               if math.gcd(n, s) == 1)
                self.assertLess(abs(completed - original), 1e-10)

    def test_cofactor_phase_and_common_ratio_cutoff_are_identical(self):
        for s in (6, 9, 30):
            for e in divisors(s):
                d = s // e
                for c, k in ((1, 2), (5, 3)):
                    j, n = -k, e * k
                    self.assertEqual(F(j * c, d), F(-c * n, s))
                    self.assertEqual(F(-j * c * e, 11), F(c * n, 11))

    def test_dropping_large_cofactors_breaks_exclusion(self):
        s, n = 6, 6
        full = sum(mobius(e) for e in divisors(math.gcd(s, n)))
        self.assertEqual(full, 0)
        self.assertEqual(mobius(1), 1)
        self.assertNotEqual(full, mobius(1))

    def test_squarefree_quotient_restoration(self):
        for a in range(1, 31):
            for v in range(1, 81):
                expected = mobius(v) ** 2 * int(math.gcd(v, a) == 1)
                self.assertEqual(squarefree_restoration(a, v), expected)

    def test_type_restoration_commutes_with_common_ratio_weight(self):
        for s in (5, 12, 17):
            for cutoff in (1, 2, 5):
                original, restored = F(0), F(0)
                for r in range(cutoff + 1, 45):
                    common = F(r + s, r * s + 1) * int(math.gcd(r, s) == 1)
                    original += mobius(r) * mobius(s) * common
                    coeff = -sum(value * int(math.gcd(a, b) == 1)
                                 * squarefree_restoration(a * b, v)
                                 for a, b, v, value in type_terms(r, cutoff))
                    restored += coeff * mobius(s) * common
                self.assertEqual(original, restored)

    def test_direct_original_double_completion_sign(self):
        for s in (4, 5, 9):
            samples = nonseparable_samples(s, s)
            for r in range(1, s):
                if math.gcd(r, s) != 1:
                    continue
                original = sum(samples[h][v] * exp2pi(F(-pow(r, -1, s) * h * v, s))
                               for h in range(s) for v in range(s))
                completed = discrete_kernel(samples, F(-r, s))
                # The unnormalized finite DFT includes the original grid mass.
                self.assertLess(abs(completed - s * original), 1e-9)

    def test_deformed_rational_completion_requires_deformed_samples(self):
        samples = nonseparable_samples(6, 9)
        theta, eta = F(1, 3), F(1, 17)
        transformed = dft2(samples)
        deformed = [[value * exp2pi(-eta * k * l)
                     for l, value in enumerate(row)]
                    for k, row in enumerate(transformed)]
        inverse = inverse_dft2(deformed)
        original = discrete_kernel(samples, theta + eta)
        self.assertLess(abs(original - rational_samples(inverse, theta)), 1e-8)
        self.assertGreater(abs(original - rational_samples(samples, theta)), 1)

    def test_packet_phase_and_q_normalization(self):
        for p, q in ((1, 1), (1, 2), (2, 3), (3, 2)):
            for s, r in ((11, 17), (17, 22), (30, 41)):
                h, length, r_scale = 7, 9, 20
                p_scale, q_scale = F(s, h), F(s, length)
                w = q * r - p * s
                w_scale = F(h * length, s)
                z = F(w, q) / w_scale
                self.assertEqual(F(-p, q) - z / (p_scale * q_scale), F(-r, s))
                self.assertEqual(F(h * length, r_scale * s) * p_scale * q_scale / q,
                                 F(s, r_scale * q))

    def test_packet_reindexing_preserves_gcd_and_exact_weight(self):
        r_scale, hl = 20, 80
        for p, q in ((1, 1), (1, 2), (2, 3), (3, 2)):
            def value(s, r):
                z = F((q * r - p * s) * s, q * hl)
                x = F(r, r_scale)
                return (mobius(r) * mobius(s) * F(s, r_scale * q)
                        * interior_weight(x) * interior_weight(abs(z)) / (1 + z * z + x * x))
            original = sum(value(s, r) for s in range(21, 40) for r in range(1, 40)
                           if math.gcd(r, s) == 1)
            restored = F(0)
            for s in range(21, 40):
                for w in range(-p * s + q, 40 * q - p * s):
                    if (p * s + w) % q:
                        continue
                    r = (p * s + w) // q
                    if math.gcd(r, s) == 1:
                        restored += value(s, r)
            self.assertEqual(original, restored)

    def test_gcd_of_shift_cannot_replace_primitive_pair(self):
        p, q, s, r = 1, 2, 6, 5
        w = q * r - p * s
        self.assertEqual(w, 4)
        self.assertEqual(math.gcd(r, s), 1)
        self.assertEqual(math.gcd(w, s), 2)
        for s in range(2, 20):
            for q in range(1, 8):
                if math.gcd(q, s) != 1:
                    continue
                for r in range(1, 20):
                    self.assertEqual(math.gcd(r, s), math.gcd(q * r - s, s))

    def test_congruence_window_count_does_not_cost_q(self):
        for q in (1, 3, 11):
            for width in (F(1, 3), F(3, 2), F(10)):
                for residue in range(q):
                    count = sum(q * width < w < 2 * q * width and w % q == residue
                                for w in range(math.ceil(2 * q * width)))
                    self.assertLessEqual(count, width + 1)

    def test_interior_support_is_not_the_dyadic_edge(self):
        height = 1000
        r_scale, hl = height ** 3, height ** 5
        s_edge = r_scale
        w_edge = F(16 * hl, s_edge)
        self.assertEqual(interior_weight(F(s_edge, r_scale) + w_edge / r_scale), 0)
        s_interior = F(3 * r_scale, 2)
        w_interior = 16 * hl / s_interior
        self.assertGreater(interior_weight(s_interior / r_scale + w_interior / r_scale), 0)

    def test_periodicity_does_not_reduce_the_physical_weight(self):
        theta, reduced = F(-101, 100), F(-1, 100)
        self.assertLess(abs(ratio_kernel(theta) - ratio_kernel(reduced)), 1e-10)
        self.assertGreater(interior_weight(-theta * F(3, 2)), 0)
        self.assertEqual(interior_weight(-reduced * F(3, 2)), 0)

    def test_profile_min_condition_differs_from_exact_zero_max(self):
        p_scale, q_scale, denominator = 4, 100, 25
        self.assertLessEqual(denominator, max(p_scale, q_scale) / 2)
        self.assertGreater(denominator, min(p_scale, q_scale))


if __name__ == "__main__":
    unittest.main(verbosity=2)
