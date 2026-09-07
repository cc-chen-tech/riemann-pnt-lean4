#!/usr/bin/env python3
"""Exact scalar certificates and finite checks; NOT an arithmetic moment proof.

The rational certificate uses alternating arctangent (Machin), the positive
atanh series for logarithms, and elementary exponential/erf inequalities.
Displayed floats and the theta optimization are illustrative only. Neither
zero exclusion nor a bridge for all heights is certified by this script.
"""

from fractions import Fraction as Q
import math
import unittest


TV = 3 * 10 ** 12
SIGMA = Q(14, 17)


def atan_bounds(x, count=12):
    assert 0 < x < 1 and count >= 1
    partial = sum(((-1) ** k * x ** (2 * k + 1) / (2 * k + 1)
                   for k in range(count)), Q(0))
    next_partial = partial + (-1) ** count * x ** (2 * count + 1) / (2 * count + 1)
    return min(partial, next_partial), max(partial, next_partial)


def pi_bounds():
    # Machin: pi = 16 atan(1/5) - 4 atan(1/239).
    a, b = atan_bounds(Q(1, 5))
    c, d = atan_bounds(Q(1, 239))
    return 16 * a - 4 * d, 16 * b - 4 * c


def log_bounds(x, count=100):
    assert x > 1 and count >= 1
    z = (x - 1) / (x + 1)
    partial = 2 * sum((z ** (2 * k + 1) / (2 * k + 1)
                       for k in range(count)), Q(0))
    remainder = 2 * z ** (2 * count + 1) / ((2 * count + 1) * (1 - z * z))
    return partial, partial + remainder


def exp_upper_small(x):
    assert 0 <= x < 3
    # n! >= 2 * 3^(n-2) for n>=2.
    return 1 + x + x * x / (2 * (1 - x / 3))


def exp_lower(x, order=12):
    assert x >= 0
    return sum((x ** k / math.factorial(k) for k in range(order + 1)), Q(0))


def certificate():
    pi_lo, pi_hi = pi_bounds()
    log3_lo, log3_hi = log_bounds(Q(3))
    log10_lo, log10_hi = log_bounds(Q(10))
    log_lo, log_hi = log3_lo + 12 * log10_lo, log3_hi + 12 * log10_hi
    # Coarser rational bounds keep the final display certificate small.
    assert Q(718, 25) < log_lo < log_hi < Q(1437, 50)  # 28.72 < log T < 28.74
    h_lo, h_hi = Q(50, 1437), Q(25, 718)
    sqrt20_lo = Q(447213, 100000)
    sqrtpi_hi = Q(88623, 50000)
    assert sqrt20_lo ** 2 < 20
    assert sqrtpi_hi ** 2 > pi_hi
    z_lo = sqrt20_lo * h_lo
    # erf(z) >= (2/sqrt(pi))*(z-z^3/3), using exp(-u^2)>=1-u^2.
    # Use monotonicity of erf before replacing z by its lower bound.
    erfc_hi = 1 - 2 * (z_lo - z_lo ** 3 / 3) / sqrtpi_hi
    assert 0 < erfc_hi < 1
    kernel_hi = pi_hi / h_lo * exp_upper_small(40 * h_hi ** 2) * erfc_hi
    # N=floor(T^(30/17)) >= T^(3/2)/2 > T*10^6/2 at TV.
    assert Q(30, 17) > Q(3, 2) and TV > 10 ** 12
    assert 10 * (2 - SIGMA) ** 2 < 14 and pi_hi < 10
    right_hi = Q(4 * 3 ** 14, TV * 10 ** 6)  # exp(14)<3^14, sqrt(pi/10)<1
    # 14-5T²/2 <= -2T; exp(T)>=T³/6; sqrt(T)>=1.
    assert 14 - Q(5, 2) * TV ** 2 < -2 * TV
    horizontal_hi = Q(5580, TV ** 5)
    remainder_hi = right_hi + horizontal_hi
    signal_lo = (2 * pi_lo - remainder_hi) ** 2 / kernel_hi
    error_hi = 1 / exp_lower(Q(7, 289) * Q(718, 25))
    return dict(signal_lo=signal_lo, error_hi=error_hi, remainder_hi=remainder_hi,
                kernel_hi=kernel_hi, log_lo=log_lo, log_hi=log_hi)


def kernel(d, lam):
    return math.pi / d * math.exp(4 * lam * d * d) * math.erfc(math.sqrt(2 * lam) * d)


def midpoint(fn, left, right, count=20000):
    step = (right - left) / count
    return step * sum(fn(left + (j + 0.5) * step) for j in range(count))


def exponents(theta):
    return (39 * theta - 68) / 34, (11 - 6 * theta) / 17, (11 * theta - 17) / 17


def optimized_model(gain):
    assert gain >= 0
    if gain <= Q(3, 17):
        return Q(30, 17) - Q(2, 3) * gain, Q(7, 289) + Q(4, 17) * gain
    return Q(28, 17), Q(19, 289)


def toy_finite_terms(theta, log_t):
    return tuple(math.exp(-float(d) * log_t) for d in exponents(theta))


def toy_minimizer(log_t):
    left, right = 17 / 11, 11 / 6
    for _ in range(100):
        point = (left + right) / 2
        a, o, m = toy_finite_terms(point, log_t)
        if -39 / 34 * a + 6 / 17 * o - 11 / 17 * m < 0:
            left = point
        else:
            right = point
    return (left + right) / 2


class GaussianCauchyChecks(unittest.TestCase):
    def test_machin_bounds_are_rational_and_enclose_coarse_pi(self):
        lo, hi = pi_bounds()
        self.assertLess(Q(314159, 100000), lo)
        self.assertLess(lo, hi)
        self.assertLess(hi, Q(3927, 1250))  # 3.1416

    def test_log_certificate_uses_positive_series_with_remainder(self):
        result = certificate()
        self.assertLess(Q(718, 25), result["log_lo"])
        self.assertLess(result["log_hi"], Q(1437, 50))
        self.assertLess(result["log_hi"] - result["log_lo"], Q(1, 10 ** 12))

    def test_strict_conditional_signal_gap_is_exact_rational(self):
        result = certificate()
        self.assertGreater(result["signal_lo"], Q(63, 125))  # .504
        self.assertLess(result["error_hi"], Q(499, 1000))
        self.assertGreater(result["signal_lo"], result["error_hi"])

    def test_other_edges_are_small_without_mobius_cancellation(self):
        self.assertLess(certificate()["remainder_hi"], Q(2, 10 ** 11))

    def test_gaussian_kernel_integral_normalization(self):
        for d, lam in ((0.035, 10), (0.1, 1), (0.2, 10)):
            radius = 10 / math.sqrt(lam)
            numerical = math.exp(2 * lam * d * d) * midpoint(
                lambda y: math.exp(-2 * lam * y * y) / (d * d + y * y), -radius, radius)
            self.assertLess(abs(numerical - kernel(d, lam)), 1e-8)

    def test_double_exponential_factor_cannot_be_dropped(self):
        d, lam = 0.2, 10
        wrong = math.pi / d * math.exp(2 * lam * d * d) * math.erfc(math.sqrt(2 * lam) * d)
        self.assertGreater(kernel(d, lam), 2 * wrong)

    def test_uniform_beta_range_and_monotonicity_cut_are_exact(self):
        self.assertLess(Q(3, 17) + Q(1, 25), Q(11, 50))
        self.assertLess(Q(11, 50) ** 2, Q(1, 20))
        self.assertLess(80 * Q(1, 10) ** 2, 1)
        pi_lo, pi_hi = pi_bounds()
        self.assertLess(pi_hi / 20, Q(4, 25))
        self.assertGreater(25 * pi_lo - 18, 57)

    def test_float_uniform_check_is_only_a_regression(self):
        h = 1 / math.log(TV)
        maximum = kernel(h, 10)
        for j in range(501):
            d = h + (1 - 14 / 17) * j / 500
            self.assertLessEqual(kernel(d, 10), maximum + 1e-12)

    def test_asymptotic_signal_retains_inverse_log_scale(self):
        for h in (1e-3, 1e-4, 1e-5):
            ratio = (2 * math.pi) ** 2 / kernel(h, 10) / (4 * math.pi * h)
            self.assertLess(abs(ratio - 1), 6 * h)

    def test_two_distinct_constraints_attain_seven_over_289(self):
        a, o, m = exponents(Q(30, 17))
        self.assertEqual((a, o, m), (Q(7, 289), Q(7, 289), Q(41, 289)))

    def test_repairing_inner_only_has_exact_piecewise_value(self):
        for gain in (Q(0), Q(1, 100), Q(1, 10), Q(3, 17), Q(1, 2), Q(2)):
            theta, margin = optimized_model(gain)
            a, o, m = exponents(theta)
            self.assertEqual(min(a + gain, o, m), margin)
            for competitor in (Q(3, 2), Q(17, 11), Q(28, 17), Q(30, 17), Q(11, 6), Q(2)):
                ca, co, cm = exponents(competitor)
                self.assertLessEqual(min(ca + gain, co, cm), margin)

    def test_outer_and_diagonal_cap_and_endpoint_inner_gain(self):
        a, o, m = exponents(Q(28, 17))
        self.assertEqual(o, m)
        self.assertEqual(o, Q(19, 289))
        self.assertEqual(a + Q(3, 17), o)
        self.assertLess(float(o), math.log(math.log(TV)) / math.log(TV))

    def test_finite_theta_stationarity_uses_error_derivatives(self):
        log_t = math.log(TV)
        theta = toy_minimizer(log_t)
        a, o, m = toy_finite_terms(theta, log_t)
        self.assertLess(abs(-39 / 34 * a + 6 / 17 * o - 11 / 17 * m), 1e-13)
        self.assertAlmostEqual(theta, 1.792713446095441)
        self.assertGreater(a + o + m, 0.87)
        self.assertLess(a + o + m, sum(toy_finite_terms(30 / 17, log_t)))

    def test_two_term_formula_has_four_thirteenths_ratio(self):
        log_t = math.log(TV)
        ca, co, ba, bo = 2, 3, 1, 0
        theta = 30 / 17 + 2 / (3 * log_t) * math.log(13 * ca / (4 * co) * log_t ** (ba - bo))
        a, o, _ = exponents(theta)
        ea, eo = ca * log_t ** ba * math.exp(-a * log_t), co * log_t ** bo * math.exp(-o * log_t)
        self.assertAlmostEqual(ea / eo, 4 / 13)

    def test_three_unit_constants_are_not_one_total_unit_constant(self):
        log_t = math.log(TV)
        total = sum(toy_finite_terms(30 / 17, log_t))
        claimed_one = math.exp(-7 / 289 * log_t)
        self.assertGreater(total, 2 * claimed_one)
        self.assertGreater(total, (2 * math.pi) ** 2 / kernel(1 / log_t, 10))

    def test_squared_line_shift_cost_is_retained(self):
        theta, h = Q(30, 17), Q(1, 25)
        self.assertEqual(2 * theta * h, Q(12, 85))
        self.assertGreater(2 * theta * h, Q(7, 289))

    def test_one_height_success_does_not_give_a_continuous_bridge(self):
        pi_lo, pi_hi = pi_bounds()
        sqrt20_hi, sqrtpi_lo = Q(223607, 50000), Q(35449, 20000)
        self.assertGreater(sqrt20_hi ** 2, 20)
        self.assertLess(sqrtpi_lo ** 2, pi_lo)
        erfc_lo = 1 - 2 * sqrt20_hi / (45 * sqrtpi_lo)
        # Drop exp(40/45²)>1; exp upper gives a lower bound on exp(-delta*45).
        ratio_lo = 45 * erfc_lo / (4 * pi_hi * exp_upper_small(Q(315, 289)))
        self.assertGreater(ratio_lo, 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
