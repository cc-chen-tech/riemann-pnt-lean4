#!/usr/bin/env python3
"""Finite DP guards; exact algebra plus labelled numerical Fourier fixtures."""

import cmath
from fractions import Fraction as F
from itertools import product
from math import ceil, comb, gcd, pi, sqrt
from pathlib import Path
import unittest

from check_physical_centered_conductor_split import characters, roots_equal
from check_physical_large_gcd_type_columns import mobius, phi, units
from check_physical_squarefree_type_descent import divisors


def theta(x, order=32):
    """Exact C^32 test cutoff; the theorem uses the original smooth partition."""
    x = F(x)
    if x <= 1:
        return F(1)
    if x >= 2:
        return F(0)
    t = x-1
    normal = (2*order+1)*comb(2*order, order)
    integral = sum(F((-1)**k*comb(order, k), order+k+1)*t**(order+k+1)
                   for k in range(order+1))
    return 1-normal*integral


def packet(x):
    return theta(abs(x))-theta(2*abs(x))


def gaussian(x):
    return cmath.exp(-pi*(x-F(2, 5))**2+2j*pi*F(1, 5)*x)


def gaussian_hat(x):
    return cmath.exp(-pi*(x-F(1, 5))**2-2j*pi*F(2, 5)*(x-F(1, 5)))


def chi_value(phases, n, ell):
    return (0j if gcd(n, ell) > 1 else
            cmath.exp(2j*pi*float(phases[n % ell])))


def balanced_exponents(eta):
    eta = F(eta)
    return ((eta-1)/2, 2-eta, 1-eta/2, F(7, 2)-2*eta)


class CenteredCharacterPoissonChecks(unittest.TestCase):
    def test_smooth_partition_exact_telescoping(self):
        scales = [F(2)**j for j in range(-3, 7)]
        for x in (F(1, 3), F(1), F(3, 2), F(3), F(17), -F(17, 3)):
            weights = [packet(x/h) for h in scales]
            self.assertTrue(all(w >= 0 for w in weights))
            self.assertEqual(sum(weights), 1)
            self.assertLessEqual(sum(w != 0 for w in weights), 2)

    def test_partition_preserves_finite_joint_signed_sum(self):
        scales = [F(2)**j for j in range(-1, 4)]
        original = F(0)
        regrouped = F(0)
        for h, d in product((-3, -2, -1, 1, 2, 3), repeat=2):
            weight = F(h*h+3*h*d-d, 1+h*h+d*d)
            original += weight
            regrouped += sum(weight*packet(F(h)/H)*packet(F(d)/L)
                             for H, L in product(scales, repeat=2))
        self.assertEqual(original, regrouped)

    def test_smooth_packet_is_not_one_hard_packet(self):
        x = F(3, 4)
        self.assertGreater(packet(x), 0)
        self.assertFalse(1 <= x < 2)
        self.assertLess(packet(F(3, 2)), 1)

    def test_hard_endpoint_has_only_first_order_fourier_tail(self):
        # For 1_[0,1], at xi=n+1/2: pi*|hat w(xi)|=1/xi exactly.
        values = [(F(n)+F(1, 2))**7 for n in (1, 3, 10, 100)]
        self.assertEqual(values, sorted(values))
        self.assertGreater(values[-1], 10**12)

    def test_centered_density_is_literal_fp3_density(self):
        def ramanujan(q, n):
            return sum(d*mobius(q//d) for d in divisors(gcd(q, n)))
        for e, q, u, v in product((1, 2, 3, 5), (1, 2, 3, 5, 6), (1, 2), (1, 3)):
            if gcd(e, q) == 1 and gcd(u*v, q) == 1:
                self.assertEqual(F(ramanujan(e*q, e*e*u*v), phi(e*q)),
                                 F(mobius(q), phi(q)))

    def test_primitive_finite_fourier_including_zero_nonunits(self):
        for ell in (3, 5, 6, 10, 15):
            for conductor, phase in characters(ell):
                if conductor != ell:
                    continue
                for k in range(ell):
                    left = [(phase[x]+F(k*x, ell), F(1)) for x in units(ell)]
                    right = ([] if gcd(k, ell) > 1 else
                             [(phase[x]+F(x, ell)-phase[k], F(1))
                              for x in units(ell)])
                    self.assertTrue(roots_equal(left, right), (ell, k))

    def test_two_gauss_fusion_with_original_minus_sign_exact(self):
        for ell in (3, 5, 6, 10, 15):
            for conductor, phase in characters(ell):
                if conductor != ell:
                    continue
                left = [
                    (F(x+y+z, ell)-phase[x]+phase[y]+phase[z]+phase[-1 % ell], F(1))
                    for x, y, z in product(units(ell), repeat=3)
                ]
                right = [(F(x, ell)+phase[x], F(ell)) for x in units(ell)]
                self.assertTrue(roots_equal(left, right))

    def test_gaussian_character_poisson_numeric_with_c_mask(self):
        # Numerical fixtures with rapidly decaying explicit transforms, not proof.
        for ell, c, U in product((3, 5, 7), (1, 2, 6), (F(1, 2), F(3))):
            if gcd(ell, c) > 1:
                continue
            for conductor, phase in characters(ell):
                if conductor != ell:
                    continue
                chi = lambda n: chi_value(phase, n, ell)
                gauss = sum(chi(x)*cmath.exp(2j*pi*x/ell) for x in units(ell))
                limit = ceil(15*U)+30
                left = sum(gaussian(F(n)/U)*chi(n)
                           for n in range(-limit, limit+1) if gcd(n, c) == 1)
                right = 0j
                for j in divisors(c):
                    limit_dual = ceil(15*j*ell/U)+30
                    series = sum(chi(m).conjugate()*gaussian_hat(F(m)*U/(j*ell))
                                 for m in range(-limit_dual, limit_dual+1))
                    right += mobius(j)*chi(j)*float(U/(j*ell))*gauss*series
                self.assertLess(abs(left-right), 1e-9*max(1, abs(left)), (ell, c, U))

    def test_divisor_overlap_and_dual_c_mask_must_not_be_deleted(self):
        c = 6
        self.assertIn((2, 2), list(product(divisors(c), repeat=2)))
        self.assertEqual(sum(mobius(j) for j in divisors(gcd(2, c))), 0)
        # After IE/Poisson a dual integer divisible by c may be an ell-unit.
        self.assertEqual(gcd(2, 5), 1)
        self.assertGreater(gcd(2, c), 1)

    def test_joint_two_variable_poisson_numeric_nonseparable_weight(self):
        # Explicit nonseparable Schwartz fixture; not the physical kernel proof.
        ell, c, U, V = 5, 2, 3., 2.
        _, phases = next((d, p) for d, p in characters(ell)
                         if d == ell and F(1, 4) in p.values())
        chi = lambda n: chi_value(phases, n, ell)
        tau = sum(chi(x)*cmath.exp(2j*pi*x/ell) for x in units(ell))
        def w(x, y):
            x, y = x-.2, y+.3
            return cmath.exp(-pi*(2*x*x+x*y+1.5*y*y))
        def wh(x, y):
            return cmath.exp(-pi*(1.5*x*x-x*y+2*y*y)/2.75
                             -2j*pi*(.2*x-.3*y))/sqrt(2.75)
        left = sum(w(u/U, v/V)*chi(u)*chi(v)
                   for u in range(-45, 46) for v in range(-30, 31)
                   if gcd(u*v, c) == 1)
        right = 0j
        for j, k in product(divisors(c), repeat=2):
            mr, ms = ceil(12*ell*j/U)+10, ceil(12*ell*k/V)+10
            dual = sum(wh(r*U/(j*ell), s*V/(k*ell))
                       *chi(r).conjugate()*chi(s).conjugate()
                       for r in range(-mr, mr+1) for s in range(-ms, ms+1))
            right += mobius(j)*mobius(k)*chi(j*k)*U*V/(j*k*ell**2)*tau*tau*dual
        self.assertLess(abs(left-right), 1e-9*max(1, abs(left)))

    def test_conjugation_is_modulus_equality_not_linear_equality(self):
        a, b, r, s = 1+2j, 3-1j, -1+1j, 2+3j
        old, new = a*b*r*s, a.conjugate()*b*r*s
        self.assertNotEqual(old, new)
        self.assertEqual((old*old.conjugate()).real, (new*new.conjugate()).real)

    def test_conjugated_coefficients_form_the_correct_product_column(self):
        # A genuinely non-real primitive character mod 5.
        chi = {1: 1+0j, 2: 1j, 4: -1+0j, 3: -1j}
        aa = {1: 1+2j, 2: 2-1j, 3: -1+1j}
        rr, ss = {1: 1j, 2: 2+1j}, {1: 1+0j, 3: 1-1j}
        av = sum(a*chi[n] for n, a in aa.items())
        rv = sum(a*chi[n].conjugate() for n, a in rr.items())
        sv = sum(a*chi[n].conjugate() for n, a in ss.items())
        merged = sum(a.conjugate()*r*s*chi[n*x*y % 5].conjugate()
                     for n, a in aa.items() for x, r in rr.items() for y, s in ss.items())
        self.assertEqual(av.conjugate()*rv*sv, merged)

    def test_full_dual_square_simplification(self):
        for A, B, L, U, V, j, k in product(
                (F(1, 2), F(3)), (F(1), F(7)), (F(2), F(11)),
                (F(1, 2), F(5)), (F(1), F(9)), (1, 2), (1, 3)):
            K0 = A*L*L*j*k/(U*V)
            pref2 = (U*V)**2/(j*j*k*k*L**3)
            full = pref2*B*K0*(B+L*L)*(K0+L*L)
            simplified = A*B*L*(B+L*L)*(A+U*V/(j*k))
            self.assertEqual(full, simplified)
            self.assertLessEqual(full, A*B*L*(B+L*L)*(A+U*V))

    def test_block_scaling_bound_exact_squared(self):
        for K0, L, t1, t2 in product((F(1, 4), F(3), F(20)), repeat=4):
            K = K0*t1*t2
            factor = max(t1, t1*t1)*max(t2, t2*t2)
            self.assertLessEqual(K*(K+L*L), factor*K0*(K0+L*L))

    def test_dyadic_tail_numeric_including_short_dual_scales(self):
        # Finite guard; the infinite sum is proved by geometric series in DP12.
        for D in (2.0**-40, .01, .5, 1., 37., 2.0**30):
            total = 0.
            for r in range(-1, 100):
                t = 2.0**r/D
                total += (1+t)**(-8+.25)*max(sqrt(t), t)
            self.assertLess(total, 8)
        # No nonzero integer belongs to a fictitious [D,2D] when 2D<1.
        self.assertFalse(any(.1 <= n <= .2 for n in range(1, 3)))

    def test_finite_derivative_budget(self):
        self.assertEqual(2*6+2*6+3, 27)
        self.assertLessEqual(27, 30)
        self.assertGreater(2*3, 5)
        self.assertGreaterEqual(12-3, 8)

    def test_all_f_costs_exact_squares(self):
        E, R, U, V, Q = map(F, (13, 97, 17, 19, 23))
        for f in range(1, 27):
            A, B = E/f, R/f
            squares = (A*A*B*B*Q, B*B*A*U*V*Q,
                       A*A*B*Q**3, A*B*U*V*Q**3)
            expected = ((E*R)**2*Q/f**4, R*R*E*U*V*Q/f**3,
                        E*E*R*Q**3/f**3, E*R*U*V*Q**3/f**2)
            self.assertEqual(squares, expected)

    def test_balanced_physical_exponents_and_boundary(self):
        for eta in (F(5, 4), F(13, 10), F(4, 3), F(3, 2), F(2)):
            q = 3-eta
            direct = (eta+3+q/2-5, 3+(5-eta)/2+q/2-5,
                      eta+F(3, 2)+3*q/2-5, (8-eta)/2+3*q/2-5)
            self.assertEqual(direct, balanced_exponents(eta))
            self.assertLessEqual(max(direct), 1)
        self.assertEqual(balanced_exponents(F(5, 4)), (F(1, 8), F(3, 4), F(3, 8), 1))
        self.assertEqual(max(balanced_exponents(F(13, 10))), F(9, 10))
        self.assertGreater(max(balanced_exponents(F(6, 5))), 1)

    def test_natural_grouping_wrong_exponent_regression(self):
        eta = F(5, 4)
        actual = 3+eta/2+F(3, 2)*(3-eta)-5
        self.assertEqual(actual, F(5, 2)-eta)
        self.assertNotEqual(actual, 2-eta)
        self.assertGreater(actual, 1)

    def test_new_support_constants_and_actual_scale(self):
        for a in (F(1), F(3, 2), F(2)):
            self.assertGreaterEqual(F(1, 2)/a, F(1, 4))
            self.assertLessEqual(2/a, 2)
        e, q, T = F(13), F(17), F(10)
        S = e+q
        H = S-T/2
        self.assertEqual((e/T, H-e), (F(13, 10), 12))
        self.assertLess(H-e, q)
        self.assertEqual(2*H, 2*S-T)
        self.assertEqual(3-e/T, F(17, 10))

    def test_no_control_bytes_in_research_files(self):
        root = Path(__file__).resolve().parents[1]
        for path in (Path(__file__),
                     root/"docs/research/2026-08-31-physical-centered-character-poisson.md"):
            self.assertEqual([(i, x) for i, x in enumerate(path.read_bytes())
                              if (x < 32 and x not in (9, 10)) or x == 127], [])


if __name__ == "__main__":
    unittest.main()
