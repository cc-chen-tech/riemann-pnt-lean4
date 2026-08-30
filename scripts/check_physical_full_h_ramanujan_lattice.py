#!/usr/bin/env python3
"""Finite all-h guards; not a substitute for the analytic large-sieve proof."""

import cmath
from fractions import Fraction as F
from itertools import product
from math import gcd, pi
from pathlib import Path
import unittest

from check_physical_centered_conductor_split import characters, roots_equal
from check_physical_large_gcd_type_columns import mobius, phi, units
from check_physical_squarefree_type_descent import divisors


MODULI = (1, 2, 3, 5, 6, 7, 10, 15, 21, 30, 35)


def ram(q, z):
    return sum(d*mobius(q//d) for d in divisors(gcd(q, z)))


def centered(q, n, e, v, m):
    return F(ram(q, n*m+e*v))-F(mobius(q)*ram(q, m), phi(q))


def exponents(eta):
    eta = F(eta)
    return F(1, 2), F(9, 4)-eta, F(7, 4)-eta, F(7, 2)-2*eta


class FullHRamanujanChecks(unittest.TestCase):
    def test_finite_poisson_coefficient_exact(self):
        for q in MODULI[1:]:
            for n, e, v in ((1, 1, 1), (2, 1, -1), (5, 2, 1)):
                if gcd(n*e*v, q) > 1:
                    continue
                gamma = e*v*pow(n, -1, q)
                for m in range(-2, q+2):
                    left = [(F(-a*(m+gamma), q), F(1)) for a in units(q)]
                    left += [(F(-a*m, q), -F(mobius(q), phi(q)))
                             for a in units(q)]
                    self.assertTrue(roots_equal(
                        left, [(F(0), centered(q, n, e, v, m))]))

    def test_prime_formula_and_two_endpoint(self):
        for p in (2, 3, 5, 7, 11):
            for m in range(2*p):
                expected = (p*(F(int((m+1) % p == 0))-F(1, p-1))
                            if gcd(m, p) == 1 else F(0))
                self.assertEqual(centered(p, 1, 1, 1, m), expected)
        self.assertTrue(all(centered(2, 1, 1, 1, m) == 0 for m in range(8)))

    def test_m_row_mean_zero(self):
        for q in MODULI[1:]:
            self.assertEqual(sum(centered(q, 1, 1, 1, m)
                                 for m in range(q)), 0)

    def test_unit_n_row_mean_zero(self):
        for q in MODULI:
            for m in range(q):
                self.assertEqual(sum(centered(q, n, 1, 1, m)
                                     for n in units(q)), 0)

    def test_unit_v_row_mean_zero(self):
        for q in MODULI:
            for m in range(q):
                self.assertEqual(sum(centered(q, 1, 1, v, m)
                                     for v in units(q)), 0)

    def test_complex_schwartz_poisson_numeric(self):
        # Explicit Schwartz fixtures, not physical convergence certificates.
        for q, width in product((2, 3, 6, 10, 15), (0.75, 2.3)):
            x0, theta = 1.7, 0.19
            a = lambda x: cmath.exp(-pi*((x-x0)/width)**2+2j*pi*theta*x)
            ah = lambda t: width*cmath.exp(
                -pi*(width*(t-theta))**2-2j*pi*x0*(t-theta))
            lhs = sum((cmath.exp(-2j*pi*u/q)-mobius(q)/phi(q))*ah(u/q)
                      for u in range(-250, 251) if gcd(u, q) == 1)
            rhs = sum(float(centered(q, 1, 1, 1, m))*a(m)
                      for m in range(-60, 61))
            self.assertLess(abs(lhs-rhs), 1e-10*max(1, abs(rhs)))

    def test_nonunit_m_descent_exact(self):
        for q in MODULI:
            for n, m in product(units(q), range(q)):
                for e, v in ((1, 1), (2, -1), (5, 2)):
                    if gcd(e*v, q) > 1:
                        continue
                    g = gcd(m, q)
                    ell = q//g
                    expected = mobius(g)*(F(ram(ell, n*m+e*v))-F(1, phi(ell)))
                    self.assertEqual(centered(q, n, e, v, m), expected)

    def test_exact_conductor_spectrum(self):
        for q in MODULI:
            for ell, ph in characters(q):
                lhs = [(-ph[w], F(ram(q, w+1))-F(1, phi(q)))
                       for w in units(q)]
                rhs = [] if ell == 1 else [(-ph[-1 % q], F(ell))]
                self.assertTrue(roots_equal(lhs, rhs), (q, ell))

    def test_outer_mobius_divisor_fusion(self):
        for q in MODULI:
            for n, m in product(units(q), range(q)):
                expected = sum(mobius(d)*d for d in divisors(gcd(q, n*m+1)))
                expected -= F(ram(q, m), phi(q))
                self.assertEqual(mobius(q)*centered(q, n, 1, 1, m), expected)

    def test_g_layer_unique_with_full_inactive_mask(self):
        for q in MODULI:
            for m in range(1, 41):
                valid = [g for g in divisors(gcd(m, q))
                         if gcd(m//g, q//g) == 1]
                self.assertEqual(valid, [gcd(m, q)])

    def test_all_conductors_and_principal_endpoints(self):
        for q in MODULI:
            self.assertEqual(len(characters(q)), phi(q))
            self.assertEqual(sum(ell == 1 for ell, _ in characters(q)), 1)
        self.assertFalse(any(ell == 2 for ell, _ in characters(2)))
        self.assertTrue(all(centered(1, 1, 1, 1, m) == 0 for m in range(5)))

    def test_complete_ie_sign_not_squarefree_e_average(self):
        for f, a, b in product(range(1, 10), repeat=3):
            left = mobius(f)*mobius(f*a)*mobius(f*b)
            right = mobius(f)*mobius(a)*mobius(b) if gcd(a*b, f) == 1 else 0
            self.assertEqual(left, right)
        self.assertNotEqual(mobius(3), mobius(3)**2)

    def test_complete_complex_f_g_c_reconstruction(self):
        primitive = {q: [(d, p) for d, p in characters(q) if d == q]
                     for q in MODULI}
        for q0, q in product((1, 2, 5), (2, 3, 5, 6, 10, 15, 21, 30)):
            if gcd(q0, q) > 1:
                continue
            direct, expanded = [], []
            for e, n, m, v in product(range(1, 6), range(1, 7),
                                       range(1, 7), (-2, -1, 1, 2)):
                if gcd(e*n, q0*q) > 1 or gcd(v, q) > 1:
                    continue
                weight = F(e+2*n-m*v+q, 11+e*n+m*m+v*v)
                phase = F((e*n+m*v+q) % 4, 4)
                if gcd(e, n) == 1:
                    direct.append((phase, weight*mobius(e)*mobius(n)*mobius(q)
                                   *centered(q, n, e, v, m)))
                for f in divisors(gcd(e, n)):
                    a, b = e//f, n//f
                    if not mobius(f)*mobius(a)*mobius(b) or gcd(a*b, f) > 1:
                        continue
                    for g in divisors(gcd(m, q)):
                        z = m//g
                        for c in divisors(q//g):
                            ell = q//(g*c)
                            if ell == 1 or gcd(z, c) > 1 or gcd(v, g*c) > 1:
                                continue
                            self.assertEqual(gcd(f, q0*g*c), 1)
                            self.assertEqual(gcd(a*b, f*q0*g*c), 1)
                            if gcd(a*b*z*v, ell) > 1:
                                continue
                            for _, ph in primitive[ell]:
                                angle = (ph[-1 % ell]+ph[b % ell]+ph[g % ell]
                                         +ph[z % ell]-ph[a % ell]-ph[v % ell])
                                coef = F(mobius(f)*mobius(a)*mobius(b)
                                         *mobius(c)*mobius(ell)*ell,
                                         phi(c)*phi(ell))
                                expanded.append((phase+angle, weight*coef))
            self.assertTrue(roots_equal(direct, expanded), (q0, q))

    def test_forbidden_z_g_mask_deletes_real_coefficient(self):
        self.assertEqual(centered(6, 1, 1, 1, 4), F(3, 2))
        g, z = gcd(4, 6), 4//gcd(4, 6)
        self.assertGreater(gcd(z, g), 1)

    def test_q0_mask_is_not_implied_by_other_masks(self):
        q0, q, e, n, v = 2, 6, 1, 5, 1
        self.assertEqual(gcd(n, q0*e*q), 1)
        self.assertEqual(gcd(e, q0*q), 1)
        self.assertEqual(gcd(v, q), 1)
        self.assertNotEqual(gcd(q, q0), 1)

    def test_conjugated_character_does_not_conjugate_coefficients(self):
        chi = {1: 1+0j, 2: 1j, 3: -1j, 4: -1+0j}
        coeff = {1: 1+2j, 2: 3-1j, 3: -2+1j}
        abar_role = sum(a*chi[n].conjugate() for n, a in coeff.items())
        aconjugate = sum(a*chi[n] for n, a in coeff.items()).conjugate()
        self.assertNotEqual(abar_role, aconjugate)

    def test_product_columns_preserve_complex_coefficients(self):
        chi = {1: 1+0j, 2: 1j, 3: -1j, 4: -1+0j, 0: 0j}
        aa, vv = {1: 1+2j, 2: 2-1j}, {-2: 1j, 1: 3+2j}
        direct = sum(a*chi[n % 5].conjugate() for n, a in aa.items())
        direct *= sum(v*chi[n % 5].conjugate() for n, v in vv.items())
        grouped = sum(a*v*chi[(n*m) % 5].conjugate()
                      for n, a in aa.items() for m, v in vv.items())
        self.assertEqual(direct, grouped)

    def test_exact_four_squared_costs(self):
        for R, M, L, Q, f, g, c in product((F(1), F(2), F(5)), repeat=7):
            lam = Q/(g*c)
            P, X, Y = R*M*L/(f*f*g), R*M/(f*g), L/f
            raw = P*X*Y, P*X*lam**2, P*Y*lam**2, P*lam**4
            form = ((R*M*L)**2/(f**4*g*g),
                    (R*M*Q)**2*L/(f**3*g**4*c*c),
                    L*L*R*M*Q*Q/(f**3*g**3*c*c),
                    R*M*L*Q**4/(f*f*g**5*c**4))
            self.assertEqual(raw, form)

    def test_balanced_endpoint_and_range(self):
        self.assertEqual(exponents(F(5, 4)), (F(1, 2), F(1), F(1, 2), F(1)))
        for j in range(16):
            self.assertLessEqual(max(exponents(F(5, 4)+F(j, 20))), 1)

    def test_method_envelope_not_a_smaller_e_theorem(self):
        self.assertEqual(max(exponents(F(6, 5))), F(11, 10))
        # This is an upper-bound term, not a lower bound for the physical sum.
        self.assertGreater(exponents(F(6, 5))[-1], 1)

    def test_point_normalization_has_one_over_m(self):
        for R, S, M, K in product((F(2), F(3), F(7)), repeat=4):
            norm_squared = (R*S*M)**2/(R*S*S*S*M*K)
            self.assertEqual(norm_squared, R*M/(S*K))
            self.assertNotEqual(norm_squared/M**2, norm_squared)

    def test_point_coordinates_cancel_f_g(self):
        E, R, M, L, Q, K = map(F, (30, 100, 10, 20, 7, 5))
        alpha, beta, zeta, nu, sigma = F(3, 2), F(4, 3), F(5, 4), F(-1), F(7, 5)
        for f, g, c in product((F(1), F(2), F(5)), repeat=3):
            a, b, z, v, ell = alpha*E/f, beta*R/f, zeta*M/g, nu*L/E, sigma*Q/(g*c)
            e, n, m, q = f*a, f*b, g*z, g*c*ell
            y = (n*m+e*v)/(e*q)
            self.assertEqual(y/K, R*M/(E*Q*K)
                             *(beta*zeta+L/(R*M)*alpha*nu)/(alpha*sigma))

    def test_short_integer_support_is_empty_without_plus_one(self):
        for X in (F(1, 10), F(1, 3), F(49, 100)):
            self.assertFalse([n for n in range(1, 5) if X/2 <= n <= 2*X])
        for X in (F(1, 2), F(3, 4), F(1), F(7, 3)):
            self.assertLessEqual(len([n for n in range(1, 10) if n <= 2*X]), 2*X)

    def test_scope_and_raw_bytes(self):
        note = (Path(__file__).resolve().parents[1]/
                "docs/research/2026-08-31-physical-full-h-ramanujan-lattice.md")
        raw = note.read_bytes()
        self.assertFalse([b for b in raw if b < 32 and b not in (9, 10)])
        body = raw.decode()
        for marker in ("完整 h", "不降低 E", "内部包", "global principal",
                       "(q,q_0)", "(gc,q₀)", "A_{\\bar\\chi}", "\\mathcal B_J",
                       "原 F(|δ|/L)", "2T}{q_0RSM"):
            self.assertIn(marker, body)


if __name__ == "__main__":
    unittest.main()
