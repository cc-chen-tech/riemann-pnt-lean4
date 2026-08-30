#!/usr/bin/env python3
"""Finite regressions for the coupled rational-phase kernel.

Checks discrete completion and exact arithmetic normalization. Finite DFTs
do NOT prove infinite-order flatness of the full Schwartz series, continuous
Poisson summation, the transition limit, or any zero-free theorem.
"""

from fractions import Fraction as F
import math
import unittest

from check_cubic_comb_mode_density import divisors, exp2pi


def dft2(samples):
    rows, cols = len(samples), len(samples[0])
    roots_r = [exp2pi(F(-n, rows)) for n in range(rows)]
    roots_c = [exp2pi(F(-n, cols)) for n in range(cols)]
    partial = [[sum(samples[x][y] * roots_c[(l * y) % cols]
                    for y in range(cols)) for l in range(cols)]
               for x in range(rows)]
    return [[sum(partial[x][l] * roots_r[(k * x) % rows]
                 for x in range(rows)) for l in range(cols)]
            for k in range(rows)]


def discrete_kernel(samples, theta):
    transformed = dft2(samples)
    return sum(value * exp2pi(-theta * k * l)
               for k, row in enumerate(transformed)
               for l, value in enumerate(row))


def rational_samples(samples, theta, phase_sign=1, extra_q=False):
    rows, cols = len(samples), len(samples[0])
    a, q = theta.numerator, theta.denominator
    assert rows % q == 0 and cols % q == 0
    inverse = pow(a, -1, q) if q > 1 else 0
    total = sum(
        samples[rows * h // q][cols * v // q]
        * exp2pi(F(phase_sign * inverse * h * v, q))
        for h in range(q) for v in range(q)
    )
    return F(rows * cols, q ** (2 if extra_q else 1)) * total


def nonseparable_samples(rows, cols):
    return [[complex(F((x + 1) * (y + 2) + (x - y) ** 2, rows * cols),
                     F(x + 2 * y + 1, rows + cols))
             for y in range(cols)] for x in range(rows)]


def supported_samples(rows, cols):
    samples = [[0j for _ in range(cols)] for _ in range(rows)]
    for x, y, value in ((1, 1, 1), (1, 2, 2), (2, 1, 3), (2, 2, 5)):
        samples[x][y] = value
    return samples


class JointRationalKernelChecks(unittest.TestCase):
    def test_complete_bilinear_gauss_phase(self):
        for q in range(1, 10):
            for a in range(q):
                if math.gcd(a, q) != 1:
                    continue
                inverse = pow(a, -1, q) if q > 1 else 0
                for h, v in ((0, 0), (1, 2), (-2, 3)):
                    original = sum(exp2pi(F(-a * r * t - r * h - t * v, q))
                                   for r in range(q) for t in range(q))
                    expected = q * exp2pi(F(inverse * h * v, q))
                    self.assertLess(abs(original - expected), 1e-10)

    def test_nonseparable_discrete_completion(self):
        for q in range(1, 6):
            samples = nonseparable_samples(2 * q, 3 * q)
            for a in range(q):
                if math.gcd(a, q) != 1:
                    continue
                theta = F(a, q)
                self.assertLess(abs(discrete_kernel(samples, theta)
                                    - rational_samples(samples, theta)), 1e-8)

    def test_negative_rational_phase(self):
        samples = nonseparable_samples(10, 15)
        theta = F(-2, 5)
        self.assertLess(abs(discrete_kernel(samples, theta)
                            - rational_samples(samples, theta)), 1e-8)

    def test_denominator_is_reduced_before_completion(self):
        samples = nonseparable_samples(9, 12)
        theta = F(2, 6)
        self.assertEqual(theta.denominator, 3)
        self.assertLess(abs(discrete_kernel(samples, theta)
                            - rational_samples(samples, theta)), 1e-8)

    def test_empty_sampling_support_annihilates_full_sum(self):
        for q in (1, 2, 3, 5):
            samples = supported_samples(4 * q, 5 * q)
            theta = F(1, q)
            self.assertEqual(rational_samples(samples, theta), 0)
            self.assertLess(abs(discrete_kernel(samples, theta)), 1e-8)
            transformed = dft2(samples)
            self.assertGreater(sum(abs(x) for row in transformed for x in row), 1)

    def test_one_coordinate_gap_suffices(self):
        # The column lattice hits the support, but the row lattice misses it.
        # This checks the one-coordinate nature of the max(P,Q) condition.
        q = 3
        samples = supported_samples(4 * q, q)
        self.assertEqual(rational_samples(samples, F(1, q)), 0)
        self.assertLess(abs(discrete_kernel(samples, F(1, q))), 1e-9)

    def test_nonempty_sampling_can_be_nonzero(self):
        samples = [[0j for _ in range(6)] for _ in range(6)]
        samples[2][2] = 1
        theta = F(1, 3)
        self.assertAlmostEqual(abs(rational_samples(samples, theta)), 12)
        self.assertLess(abs(discrete_kernel(samples, theta)
                            - rational_samples(samples, theta)), 1e-9)

    def test_phase_and_prefactor_mutants_are_detected(self):
        samples = [[0j for _ in range(15)] for _ in range(10)]
        samples[2][6] = 1
        theta = F(2, 5)
        original = discrete_kernel(samples, theta)
        self.assertLess(abs(original - rational_samples(samples, theta)), 1e-9)
        self.assertGreater(abs(original - rational_samples(samples, theta,
                                                            phase_sign=-1)), 1)
        self.assertGreater(abs(original - rational_samples(samples, theta,
                                                            extra_q=True)), 1)

    def test_full_mode_order_cannot_be_replaced_by_a_single_mode(self):
        samples = supported_samples(12, 15)
        self.assertGreater(abs(dft2(samples)[0][0]), 1)
        self.assertLess(abs(discrete_kernel(samples, F(0))), 1e-9)

    def test_nonzero_mode_density_has_no_extra_one(self):
        for step in (F(1, 20), F(1, 2), F(1), F(7), F(50)):
            for order in (2, 3, 5):
                partial = 2 * sum((1 + step * j) ** (-order)
                                  for j in range(1, 81))
                bound = 2 / (step * (order - 1))
                self.assertLessEqual(partial, bound)
        # j=0 would invalidate the same bound when the step is large.
        self.assertGreater(1, F(2, 50 * (2 - 1)))

    def test_squarefree_completion_jacobian_is_exact(self):
        for a in (1, 6, 35):
            for t in (1, 3, 10):
                for b in divisors(a):
                    c = a * t * t * b
                    for d, e, h, length in ((7, 2, 3, 4), (19, 5, 13, 17)):
                        p, q = F(d * e, h), F(d * e, length)
                        before = F(1, c) * F(h * length, d * e * e) * F(c, d)
                        after = F(h * length, d * d * e * e)
                        self.assertEqual(before, after)
                        self.assertEqual(after * p * q, 1)

    def test_square_divisor_and_divisor_layer_density(self):
        for a in range(1, 25):
            for d in (3, 17):
                exact_positive_sum = sum(F(d, a * t * t * b)
                                         for t in range(1, 18)
                                         for b in divisors(a))
                factorized = (F(d, a) * sum(F(1, t * t) for t in range(1, 18))
                              * sum(F(1, b) for b in divisors(a)))
                self.assertEqual(exact_positive_sum, factorized)

    def test_all_cofactor_count_includes_small_d_endpoints(self):
        for scale in (F(1), F(3, 2), F(7), F(41, 2)):
            total = 0
            limit = math.ceil(2 * scale)
            for e in range(1, limit):
                inner = sum(d for d in range(1, limit) if scale < d * e < 2 * scale)
                self.assertLessEqual(inner, 6 * (scale / e) ** 2)
                total += inner
            self.assertLessEqual(total, 6 * scale * scale
                                 * sum(F(1, e * e) for e in range(1, limit)))

    def test_divisor_coefficient_mass_bound(self):
        for limit in (5, 20, 60):
            harmonic = sum(F(1, n) for n in range(1, limit + 1))
            mass = sum(F(len(divisors(a)), a) * sum(F(1, b) for b in divisors(a))
                       for a in range(1, limit + 1))
            self.assertLessEqual(mass, harmonic ** 3)

    def test_deep_arc_power_and_transition_are_distinct(self):
        delta = F(1, 100)
        order = 701
        self.assertLess(F(6) - order * delta, -1)
        for frequency_scale in (10, 20, 100):
            pq = frequency_scale ** 2
            theta = F(16, pq)
            self.assertEqual(theta * pq, 16)
            self.assertGreater(theta, F(1, pq))
        # Only the stated nonnegative kernel gives the sharpness witness:
        # for 1<x,y<2, xy/16 is strictly between 0 and 1/4.
        for x, y in ((F(5, 4), F(7, 4)), (F(3, 2), F(3, 2))):
            self.assertLess(x * y / 16, F(1, 4))
            self.assertGreater(exp2pi(x * y / 16).real, 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
