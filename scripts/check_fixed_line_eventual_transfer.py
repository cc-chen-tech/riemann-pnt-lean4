#!/usr/bin/env python3
"""Finite checks accompanying a conditional analytic transfer, not a zeta proof.

Run with Python's standard library only.  Polytope and rational identities are
exact; the explicitly named numerical regressions check conventions only.
"""

from fractions import Fraction as F
from itertools import combinations, product
import cmath
import math
import unittest


# Affine functions of (q, Delta, tau), constant first.
def affine(c=0, q=0, d=0, t=0):
    return tuple(map(F, (c, q, d, t)))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def sub(a, b):
    return add(a, neg(b))


def scale(a, c):
    return tuple(x * c for x in a)


def evaluate(a, point):
    return a[0] + sum(x * y for x, y in zip(a[1:], point))


def intersection(planes):
    """Solve three independent affine equalities, or return None."""
    rows = [list(a[1:]) + [-a[0]] for a in planes]
    for j in range(3):
        pivot = next((i for i in range(j, 3) if rows[i][j]), None)
        if pivot is None:
            return None
        rows[j], rows[pivot] = rows[pivot], rows[j]
        lead = rows[j][j]
        rows[j] = [v / lead for v in rows[j]]
        for i in range(3):
            if i != j:
                lead = rows[i][j]
                rows[i] = [x - lead * y for x, y in zip(rows[i], rows[j])]
    return tuple(row[3] for row in rows)


def model_minima():
    """Exhaust all 16 affine pieces of the stated compact exponent model."""
    sigma, theta, w = F(14, 17), F(30, 17), F(13, 34)
    m = theta * (2 * sigma - 1) - 1
    q0, qfull = sigma * theta - F(1, 2), (theta + 1) / 2
    q, delta, tau = affine(q=1), affine(d=1), affine(t=1)
    kappa = sub(affine(w), delta)
    x = sub(sub(q, affine(w)), delta)
    pv = [scale(kappa, 2), sub(add(q, scale(kappa, 2)), scale(tau, 2))]
    prod = [tau, sub(add(q, kappa), tau)]
    ell = [sub(scale(q, 2), affine(theta)), affine(theta - 1)]
    base = [
        sub(q, affine(q0)), sub(affine(qfull), q), delta,
        sub(affine(w), delta), sub(sub(affine(qfull), q), delta),
        tau, sub(x, tau),
    ]
    records, nonempty = [], 0
    for ip, ir, imax, ie in product(range(2), repeat=4):
        candidates = [pv[ip], prod[ir]]
        saving = candidates[imax]
        constraints = base + [
            sub(pv[1 - ip], pv[ip]),
            sub(prod[1 - ir], prod[ir]),
            sub(saving, candidates[1 - imax]),
            sub(ell[1 - ie], ell[ie]),
        ]
        deficit = sub(ell[ie], affine(m))
        centered = sub(add(saving, delta), deficit)
        mixed = sub(
            scale(add(add(saving, delta), sub(scale(q, 2), affine(theta))), F(1, 2)),
            deficit,
        )
        vertices = set()
        for planes in combinations(constraints, 3):
            vertex = intersection(planes)
            if vertex is not None and all(evaluate(c, vertex) >= 0 for c in constraints):
                vertices.add(vertex)
        nonempty += bool(vertices)
        for vertex in vertices:
            # Independently evaluate the original nested min/max expression.
            qv, dv, tv = vertex
            kv = w - dv
            sv = max(min(2 * kv, qv + 2 * kv - 2 * tv), min(tv, qv + kv - tv))
            required = min(2 * qv - theta, theta - 1) - m
            cv = sv + dv - required
            mv = (sv + dv + 2 * qv - theta) / 2 - required
            if evaluate(centered, vertex) != cv or evaluate(mixed, vertex) != mv:
                raise ArithmeticError("Affine branch differs from nested model")
            records.append((cv, mv, vertex))
    return records, nonempty


def transfer_budget(sigma, theta, decay):
    a0 = sigma / 2
    distance = sigma - a0
    growth = 3 + 2 * theta * (1 - a0)
    maximum_shift = distance * decay / (growth + decay)
    h, eta = maximum_shift / 2, maximum_shift / 4
    exponent = -decay + (growth + decay) * h / distance
    return growth, maximum_shift, h, eta, exponent, sigma - eta


def mobius(n):
    result, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            result = -result
            if n % p == 0:
                return 0
        p += 1
    return -result if n > 1 else result


def simpson(f, lo, hi, panels=12000):
    if panels % 2:
        raise ValueError("Simpson panels must be even")
    step = (hi - lo) / panels
    return step / 3 * (
        f(lo) + f(hi)
        + 4 * sum(f(lo + j * step) for j in range(1, panels, 2))
        + 2 * sum(f(lo + j * step) for j in range(2, panels, 2))
    )


class FiniteTransferChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.vertices, cls.nonempty = model_minima()

    def test_linear_solver(self):
        self.assertEqual(
            intersection([affine(-1, q=1), affine(-2, d=1), affine(-3, t=1)]),
            (F(1), F(2), F(3)),
        )
        self.assertIsNone(intersection([affine(q=1)] * 3))

    def test_entire_centered_model(self):
        self.assertGreater(self.nonempty, 0)
        self.assertEqual(min(v[0] for v in self.vertices), F(7, 289))
        witness = (F(43, 34), F(2, 17), F(0))
        self.assertIn((F(7, 289), F(24, 289), witness), self.vertices)

    def test_entire_mixed_model(self):
        self.assertEqual(min(v[1] for v in self.vertices), F(24, 289))

    def test_outer_and_diagonal_models_are_distinct(self):
        sigma, theta = F(14, 17), F(30, 17)
        self.assertEqual((2 * sigma - 1) - 2 * (1 - sigma) * theta, F(7, 289))
        self.assertEqual(theta * (2 * sigma - 1) - 1, F(41, 289))
        self.assertEqual(2 * sigma - 1, F(11, 17))

    def test_conditional_left_shift_full_decay(self):
        self.assertEqual(
            transfer_budget(F(14, 17), F(30, 17), F(7, 289)),
            (F(1467, 289), F(49, 25058), F(49, 50116),
             F(49, 100232), -F(7, 578), F(82495, 100232)),
        )

    def test_epsilon_loss_is_paid_before_transfer(self):
        actual = transfer_budget(F(14, 17), F(30, 17), F(7, 578))
        self.assertEqual(actual[1:5],
                         (F(49, 49997), F(49, 99994), F(49, 199988), -F(7, 1156)))

    def test_strict_shift_endpoint(self):
        for sigma in (F(2, 3), F(14, 17), F(9, 10)):
            for theta in (F(1), F(30, 17), F(3)):
                for decay in (F(1, 100), F(7, 289), F(1)):
                    growth, maximum, _, _, exponent, _ = transfer_budget(sigma, theta, decay)
                    d = sigma / 2
                    self.assertLess(exponent, 0)
                    self.assertEqual(-decay + (growth + decay) * maximum / d, 0)

    def test_mobius_inverse_tail_coefficients(self):
        for cutoff in (1, 2, 7, 13, 31):
            for n in range(1, 129):
                head = sum(mobius(d) for d in range(1, min(cutoff, n) + 1) if n % d == 0)
                tail = sum(mobius(d) for d in range(cutoff + 1, n + 1) if n % d == 0)
                self.assertEqual(head + tail, int(n == 1))
                self.assertEqual(head - int(n == 1), -tail)

    def test_zero_value_pole_killer_lower_bound(self):
        for beta in (F(1, 10), F(1, 2), F(14, 17), F(1)):
            for height in (F(3), F(10), F(100)):
                quotient = ((beta - 1) ** 2 + height ** 2) / ((beta + 1) ** 2 + height ** 2)
                self.assertGreaterEqual(quotient, height ** 2 / (height ** 2 + 4))

    def test_gaussian_fourier_sign_numerical_regression(self):
        # f_x(t)=exp((x+it)^2). Its unitary Fourier modulus squared is
        # (1/2)exp(-u^2/2+2ux), so changing x uses the POSITIVE Fourier sign.
        for x in (0.0, 0.25, 0.75):
            spectral = simpson(lambda u: 0.5 * math.exp(-u * u / 2 + 2 * u * x), -14, 14)
            physical = math.sqrt(math.pi / 2) * math.exp(2 * x * x)
            self.assertAlmostEqual(spectral, physical, delta=1e-10 * physical)
        u, x0, x1 = F(3, 4), F(1, 5), F(4, 5)
        exponent_difference = (-u * u / 2 + 2 * u * x1) - (-u * u / 2 + 2 * u * x0)
        self.assertEqual(exponent_difference, 2 * u * (x1 - x0))

    def test_nonzero_frequency_detects_wrong_fourier_sign(self):
        # Unlike the integrated even Gaussian, a fixed nonzero frequency
        # distinguishes exp(+u*x) from exp(-u*x).
        for x, u in ((0.5, 1.0), (0.25, 2.0), (0.75, -0.5)):
            transformed = simpson(
                lambda t: cmath.exp((x + 1j * t) ** 2) * cmath.exp(-1j * u * t),
                -10, 10,
            ) / math.sqrt(2 * math.pi)
            expected = math.exp(-u * u / 4 + u * x) / math.sqrt(2)
            wrong_sign = math.exp(-u * u / 4 - u * x) / math.sqrt(2)
            self.assertAlmostEqual(transformed.real, expected, delta=1e-10)
            self.assertAlmostEqual(transformed.imag, 0, delta=1e-10)
            self.assertGreater(abs(transformed.real - wrong_sign), 0.1)

    def test_strip_poisson_normalization_numerical_regression(self):
        for length in (1.0, 1.5, 2.0):
            for fraction in (0.1, 0.3, 0.5, 0.8):
                r = fraction * length
                angle = math.pi * r / length
                def kernel(v):
                    return math.sin(angle) / (2 * length * (math.cosh(math.pi * v / length) - math.cos(angle)))
                mass = simpson(kernel, -20 * length, 20 * length)
                self.assertAlmostEqual(mass, 1 - fraction, delta=2e-9)
                self.assertLessEqual(kernel(0), 1 / (math.pi * r) + 1e-12)


if __name__ == "__main__":
    unittest.main(verbosity=2)
