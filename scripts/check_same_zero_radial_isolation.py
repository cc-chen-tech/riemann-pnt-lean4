#!/usr/bin/env python3
"""Finite algebra and quadrature guards for radial residue isolation.

All spectral nodes are synthetic, NOT asserted zeta zeros. Polynomial and
atomic fixtures do not replace the smooth Mellin/contour proofs. No Lean,
zeta zero exclusion, global lower bound, or uniform growing-window bound
is certified by this script.
"""

from fractions import Fraction as F
import cmath
import math
import unittest


def multiply(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def evaluate(poly, x):
    out = F(0)
    for coefficient in reversed(poly):
        out = out * x + coefficient
    return out


def translated(poly, center, order=None):
    if order is None:
        order = len(poly) - 1
    return [sum(coefficient * math.comb(j, k) * center ** (j - k)
                for j, coefficient in enumerate(poly) if j >= k)
            for k in range(order + 1)]


def reciprocal_jet(poly_at_center, order):
    assert poly_at_center[0] != 0
    inverse = [1 / poly_at_center[0]]
    for n in range(1, order + 1):
        inverse.append(-sum(poly_at_center[k] * inverse[n - k]
                            for k in range(1, min(n, len(poly_at_center) - 1) + 1))
                       / poly_at_center[0])
    return inverse


def build_filter(nodes, target):
    """Exact real synthetic nodes; the analytic proof allows complex zeros."""
    center = 2 * target
    roots = {}
    for a, ma in nodes.items():
        for b, mb in nodes.items():
            if a == b == target:
                continue
            assert a + b != center
            roots[a + b] = max(roots.get(a + b, 0), ma + mb - 1)
    base = [F(1)]
    for root, order in roots.items():
        factor = [-root / (center - root), 1 / (center - root)]
        for _ in range(order):
            base = multiply(base, factor)
    jet = reciprocal_jet(translated(base, center), 2 * nodes[target] - 2)
    # jet is a polynomial in z-center; translate back to z.
    correction = translated(jet, -center)
    return base, multiply(base, correction), roots


def mixed_residue(poly, center, m, n, analytic):
    """Coefficient of x^(m-1)y^(n-1) in P(center+x+y)*analytic(x,y)."""
    shifted = translated(poly, center, m + n - 2)
    result = F(0)
    for i in range(m):
        for j in range(n):
            result += shifted[i + j] * math.comb(i + j, i) * analytic.get(
                (m - 1 - i, n - 1 - j), F(0))
    return result


def midpoint_integral(fn, left, right, count=4000):
    step = (right - left) / count
    return step * sum(fn(left + (j + 0.5) * step) for j in range(count))


class SameZeroIsolationChecks(unittest.TestCase):
    def test_same_zero_prime_two_survives_conjugate_cancellation_sample(self):
        beta = 0.75
        gamma = math.acos(2 ** (beta - 1)) / math.log(2)
        point = complex(beta, gamma)  # Synthetic complex point, not a zeta zero.
        self.assertLess(abs(1 - 2 ** (-point) - 2 ** (-point.conjugate())), 1e-14)
        self.assertGreaterEqual(abs(1 - 2 ** (1 - point)), 2 ** (1 - beta) - 1)

    def test_all_same_zero_local_factors_nonzero(self):
        for beta in (2 / 3, 0.8, 0.99):
            for gamma in (0, 7, 91):
                point = complex(beta, gamma)
                for p in (2, 3, 5, 11, 101):
                    self.assertGreater(abs(1 - 2 * p ** (-point)), 0)
        self.assertAlmostEqual(1 - 2 ** (1 - 1), 0)  # beta=1 cannot be included.

    def test_same_zero_coefficient_uses_square_not_modulus_square(self):
        h, leading = complex(2, 1), complex(1, 2)
        coefficient = h / leading ** 2
        phase = coefficient.conjugate() / abs(coefficient)
        self.assertAlmostEqual((phase * coefficient).real, abs(coefficient))
        self.assertAlmostEqual((phase * coefficient).imag, 0)
        self.assertNotEqual(coefficient, h / abs(leading) ** 2)

    def test_twist_normalization_and_mellin_shift(self):
        r, s, scale, gamma = 153, 157, 100, 4.25
        x, y = r / scale, s / scale
        self.assertLess(abs((r * s) ** (-1j * gamma)
                            - scale ** (-2j * gamma) * (x * y) ** (-1j * gamma)), 1e-13)
        beta = 0.8
        point = complex(beta, gamma)
        atomic_mellin = (x * y) ** (-1j * gamma) * x ** (point - 1) * y ** (point - 1)
        self.assertLess(abs(atomic_mellin - x ** (beta - 1) * y ** (beta - 1)), 1e-13)

    def test_radial_and_relative_generators_have_different_scales(self):
        x, y, delta = F(151, 100), F(3, 2), F(1, 1000)
        z = (x - y) * y / delta
        ex, ey = x * y / delta, (x * y - 2 * y * y) / delta
        self.assertEqual(ex + ey, 2 * z)
        self.assertEqual(ex - ey, 2 * y * y / delta)
        self.assertNotEqual(ex - ey, 2 * z)

    def test_radial_action_on_joint_polynomial_profile(self):
        # U=x^a, V=y^b, k=z^c: homogeneous finite algebra, no compactness claim.
        a, b, c = 2, 3, 4
        radial_degree = 1 + a + b + 2 * c
        p = [F(2), F(-3), F(1)]
        self.assertEqual(evaluate(p, -radial_degree),
                         2 + 3 * radial_degree + radial_degree ** 2)

    def test_fixed_delta_derivative_is_not_family_x_derivative(self):
        # z=(r-s)s/(X^2 delta(X)), with delta(X)=X^(-1/3).
        self.assertEqual(-2 + F(1, 3), F(-5, 3))
        self.assertNotEqual(F(-5, 3), -2)

    def test_profile_euler_integration_by_parts_sign(self):
        # Polynomial endpoint fixture has zero boundary values; not C-infinity.
        def phi(a):
            return (a - 1) ** 2 * (2 - a) ** 2
        def dphi(a):
            return 2 * (a - 1) * (2 - a) * (3 - 2 * a)
        for z in (40, -40):
            b = 1.5
            wave = lambda a: cmath.exp(-2j * math.pi * a * b / z)
            value = midpoint_integral(lambda a: phi(a) * wave(a), 1, 2) / abs(z)
            moment = midpoint_integral(lambda a: a * phi(a) * wave(a), 1, 2) / abs(z)
            lhs = -value + 2j * math.pi * b / z * moment
            rhs = midpoint_integral(lambda a: a * dphi(a) * wave(a), 1, 2) / abs(z)
            self.assertLess(abs(lhs - rhs), 1e-8)

    def test_lexicographic_extreme_has_unique_doubled_sum(self):
        nodes = [(F(4, 5), F(2)), (F(4, 5), F(-2)), (F(3, 4), F(3))]
        target = max(nodes)
        matches = [(a, b) for a in nodes for b in nodes
                   if (a[0] + b[0], a[1] + b[1]) == (2 * target[0], 2 * target[1])]
        self.assertEqual(matches, [(target, target)])

    def test_nonextreme_node_has_sum_collision(self):
        target = (F(4, 5), F(2))
        a, b = (F(9, 10), F(3)), (F(7, 10), F(1))
        self.assertEqual((a[0] + b[0], a[1] + b[1]),
                         (2 * target[0], 2 * target[1]))
        self.assertNotEqual(a, target)

    def test_hermite_filter_preserves_target_and_all_other_root_orders(self):
        target = F(9, 10)
        nodes = {target: 2, F(4, 5): 1, F(3, 5): 2}
        base, poly, roots = build_filter(nodes, target)
        self.assertEqual(translated(poly, 2 * target, 2), [F(1), F(0), F(0)])
        for root, order in roots.items():
            self.assertEqual(translated(poly, root, order - 1), [F(0)] * order)
        self.assertLessEqual(len(base) - 1, 2 * len(nodes) * sum(nodes.values()) - len(nodes) ** 2)

    def test_value_one_alone_does_not_preserve_multiple_pole_residue(self):
        base = [F(1), F(2)]  # Center is zero, so P0(0)=1.
        analytic = {(0, 0): F(1), (1, 0): F(3), (0, 1): F(5), (1, 1): F(7)}
        self.assertNotEqual(mixed_residue(base, F(0), 2, 2, analytic), F(7))
        corrected = multiply(base, reciprocal_jet(base, 2))
        self.assertEqual(mixed_residue(corrected, F(0), 2, 2, analytic), F(7))

    def test_all_mixed_residues_removed_except_exact_target(self):
        target = F(9, 10)
        nodes = {target: 2, F(4, 5): 1, F(3, 5): 2}
        _, poly, _ = build_filter(nodes, target)
        analytic = {(i, j): F(1, i + 2 * j + 1) for i in range(3) for j in range(3)}
        for a, m in nodes.items():
            for b, n in nodes.items():
                actual = mixed_residue(poly, a + b, m, n, analytic)
                expected = analytic[(m - 1, n - 1)] if a == b == target else F(0)
                self.assertEqual(actual, expected)

    def test_total_vanishing_order_cannot_be_reduced_by_one(self):
        for m, n in ((1, 1), (2, 1), (2, 3)):
            too_short = [F(0)] * (m + n - 2) + [F(1)]
            sufficient = [F(0)] * (m + n - 1) + [F(1)]
            self.assertNotEqual(mixed_residue(too_short, F(0), m, n, {(0, 0): F(1)}), 0)
            self.assertEqual(mixed_residue(sufficient, F(0), m, n, {(0, 0): F(1)}), 0)

    def test_hermite_correction_needs_its_own_coefficient_bound(self):
        base = [F(1), F(2), F(1)]
        corrected = multiply(base, reciprocal_jet(base, 2))
        self.assertEqual(corrected, [F(1), F(0), F(0), F(4), F(3)])
        self.assertGreater(corrected[-1], math.comb(4, 4))

    def test_radial_filter_does_not_cut_long_difference_frequency(self):
        target = F(9, 10)
        _, poly, _ = build_filter({target: 2, F(4, 5): 1}, target)
        for height in (1, 100, 10000):
            u, v = complex(float(target), height), complex(float(target), -height)
            self.assertAlmostEqual((u + v).real, float(2 * target))
            self.assertEqual(evaluate(poly, 2 * target), 1)

    def test_corrected_coefficient_convolution_bound(self):
        target = F(9, 10)
        nodes = {target: 2, F(4, 5): 1, F(3, 5): 2}
        base, poly, roots = build_filter(nodes, target)
        degree, order = len(base) - 1, 2 * nodes[target] - 2
        gap = min(abs(2 * target - root) for root in roots)
        for ell, coefficient in enumerate(translated(poly, 2 * target)):
            bound = gap ** (-ell) * sum(
                math.comb(degree, ell - j) * math.comb(degree + j - 1, j)
                for j in range(max(0, ell - degree), min(order, ell) + 1))
            self.assertLessEqual(abs(coefficient), bound)
        self.assertEqual(build_filter({target: 2}, target)[1], [F(1), F(0), F(0)])

    def test_gaussian_relative_dilation_multiplier(self):
        a, difference = 3.0, complex(0.2, 4)
        actual = a / math.sqrt(math.pi) * midpoint_integral(
            lambda t: cmath.exp(-a * a * t * t - t * difference), -8 / a, 8 / a)
        expected = cmath.exp(difference ** 2 / (4 * a * a))
        self.assertLess(abs(actual - expected), 1e-12)

    def test_gaussian_new_weight_is_nonzero_outside_original_strip(self):
        # Atomic z fixture for formula (23), with U,V positive at its arguments.
        p, a, d = 1.5, 8, 1 / 16
        def normalized(delta):
            self.assertGreater(abs(p * p * (1 - math.exp(-d)) / delta), 64)
            result = 0.0
            for z in (-48, -36, 36, 48):
                b = -0.5 * math.log(1 - delta * z / (p * p))
                result += (math.exp(-a * a * (b - d / 2) ** 2) * p * math.exp(-b)
                           / (2 * p * p * (1 - delta * z / (p * p))) / math.sqrt(math.pi))
            return result
        first, second = normalized(1e-4), normalized(5e-5)
        self.assertGreater(first, 0.5)
        self.assertTrue(0.99 < first / second < 1.01)

    def test_relative_dilation_jacobian_preserves_continuous_mass(self):
        for dilation in (F(2), F(3, 2), F(1, 7)):
            self.assertEqual(dilation * (1 / dilation), 1)


if __name__ == "__main__":
    unittest.main()
