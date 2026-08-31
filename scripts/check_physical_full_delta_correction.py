#!/usr/bin/env python3
"""Finite guards only: they do not prove the uniform analytic kernel bounds."""

import cmath
from fractions import Fraction as F
from itertools import product
from math import exp, gcd, pi
from pathlib import Path
import unittest

from check_physical_centered_conductor_split import roots_equal
from check_physical_large_gcd_type_columns import mobius, phi, units
from check_physical_squarefree_type_descent import divisors


MODULI = (2, 3, 5, 6, 7, 10, 15, 21, 30, 35)


def ram(q, m):
    return sum(d*mobius(q//d) for d in divisors(gcd(q, m)))


class FullDeltaCorrectionTests(unittest.TestCase):
    def test_scope_contract_and_fixed_derivative_budget(self):
        note = (Path(__file__).resolve().parents[1]/
                'docs/research/2026-08-31-physical-full-delta-correction.md').read_text()
        for required in ('FD1.', 'FD7.', 'N=T³', 'KS\\asymp MR',
                         '\\kappa=\\frac{eRM}{Enm}', 'j+k≤12',
                         'qK≲T⁴', '固定 L', '新模 a', '跨 AFE 尾'):
            self.assertIn(required, note)

    def test_note_has_no_control_bytes(self):
        data = (Path(__file__).resolve().parents[1]/
                'docs/research/2026-08-31-physical-full-delta-correction.md').read_bytes()
        self.assertFalse(any(c < 32 and c not in (9, 10) for c in data))

    def test_actual_e_scaled_phase_exact(self):
        for R, M, E, T in product((2, 5), repeat=4):
            for re, rn, rm, z in product((F(1), F(3, 2)), repeat=4):
                e, n, m = E*re, R*rn, M*rm
                Vstar = F(R*M, E*T)
                kappa = F(e*R*M, E*n*m)
                self.assertEqual(1+e*Vstar*z/(n*m), 1+kappa*z/T)
        # The integer e cannot silently be replaced by its scale E.
        self.assertNotEqual(F(3*2*2, 2*2*2), F(2*2, 2*2))

    def test_outer_mobius_correction_sign(self):
        for q in MODULI:
            for m, v in product(range(q), units(q)):
                centered = F(ram(q, m+v))-F(mobius(q)*ram(q, m), phi(q))
                expanded = sum(mobius(d)*d for d in divisors(gcd(q, m+v)))
                self.assertEqual(mobius(q)*centered,
                                 expanded-F(ram(q, m), phi(q)))

    def test_complete_divisor_zero_coefficient(self):
        for q in MODULI:
            for m in range(2*q):
                lhs = sum(mobius(d)*sum(
                    (F(mobius(b), b) for b in divisors(q) if gcd(b, d) == 1), F(0))
                    for d in divisors(q) if gcd(m, d) == 1)
                self.assertEqual(lhs, F(ram(q, m), q))

    def test_correction_zero_coefficient_exact(self):
        for q in MODULI:
            for m in range(q):
                coeff = F(ram(q, m), phi(q))*sum(
                    (F(mobius(b), b) for b in divisors(q)), F(0))
                self.assertEqual(coeff, F(ram(q, m), q))

    def test_unit_ie_for_arbitrary_complex_finite_weight(self):
        # Two rational coordinates encode exact complex weights.
        for q in MODULI:
            for coord in (0, 1):
                w = lambda v: (F(v*v+2*v+1, 17+v*v) if coord == 0
                               else F(v**3-2, 31+v*v))
                direct = sum((w(v) for v in range(-47, 48) if gcd(v, q) == 1), F(0))
                completed = sum(mobius(b)*sum(
                    (w(v) for v in range(-47, 48) if v % b == 0), F(0))
                    for b in divisors(q))
                self.assertEqual(direct, completed)

    def test_grid_origin_must_be_tracked_before_ie(self):
        a0 = F(7, 13)
        for q in MODULI:
            self.assertEqual(sum(mobius(b)*a0 for b in divisors(q)), 0)
        # Removing j=0 from one grid changes its Poisson identity by A(0).
        self.assertNotEqual(a0, 0)
        self.assertEqual(sum(mobius(b)*a0 for b in divisors(1)), a0)

    def test_composite_nonunit_m_correction_not_deleted(self):
        self.assertNotEqual(F(ram(6, 2), phi(6)), 0)
        self.assertGreater(gcd(6, 2), 1)
        for q in MODULI:
            self.assertTrue(all(abs(ram(q, m)) <= phi(q) for m in range(q)))

    def test_q_one_centered_exception(self):
        self.assertEqual(ram(1, 1)-F(mobius(1)*ram(1, 1), phi(1)), 0)
        self.assertEqual(F(ram(1, 1), phi(1)), 1)

    def test_finite_delta_support(self):
        for n, s, M, K in product(range(1, 6), repeat=4):
            for x, y in product((F(M, 2), F(3*M, 2), 2*M),
                                (F(K, 2), F(3*K, 2), 2*K)):
                delta = s*y-n*x
                self.assertLessEqual(abs(delta), 2*s*K+2*n*M)

    def test_overlapping_partition_exact_finite_surrogate(self):
        # Piecewise-linear test of partition algebra, NOT smoothness proof.
        rho = lambda x: F(1) if x <= 1 else max(F(0), 2-x)
        cutoff = lambda x: rho(x)-rho(2*x)
        scales = [F(2)**j for j in range(-2, 9)]
        for delta in range(-64, 65):
            if delta:
                self.assertEqual(sum(cutoff(abs(delta)/L) for L in scales), 1)

    def test_exact_outer_squared_normalization(self):
        for R, S, E, M, K, T, q0 in product((F(1, 2), F(2), F(5)), repeat=7):
            Q = S/E
            lhs2 = (R*E*Q*M)**2/(q0*q0*R*S*S*S)*T*T/(M*K)
            rhs2 = T*T/(q0*q0)*M*R/(K*S)
            self.assertEqual(lhs2, rhs2)

    def test_mean_polynomial_derivative_budget(self):
        # q<=T^3, K<=2T (MK<=T, M>=1/2), J=6.
        for T in range(2, 60):
            self.assertLessEqual(F(2*T**4, T**6), 1)

    def test_all_x_schwartz_nonzero_sum_majorant(self):
        for x in (F(1, 100), F(1, 4), F(1), F(3), F(40)):
            finite = 2*x*sum((1+x*k)**-2 for k in range(1, 301))
            self.assertLessEqual(finite, 2)

    def test_complex_mean_zero_poisson_numeric(self):
        # Explicit Schwartz toys only; this is not the actual AFE kernel.
        theta = .37
        for V, b in product((.125, .75, 2., 16.), (1, 2, 7)):
            a = lambda v: exp(-pi*(v/V)**2)*(cmath.exp(2j*pi*theta*v/V)
                                            -exp(-pi*theta*theta))
            ah = lambda xi: V*(exp(-pi*(V*xi-theta)**2)
                               -exp(-pi*theta*theta)*exp(-pi*(V*xi)**2))
            self.assertEqual(ah(0), 0)
            lhs = sum(a(b*j) for j in range(-max(80, int(12*V/b)),
                                             max(80, int(12*V/b))+1))
            J = max(80, int(12*b/V))
            rhs = sum(ah(k/b) for k in range(-J, J+1))/b
            self.assertLess(abs(lhs-rhs), 2e-12)
            self.assertLess(abs(lhs), 4)

    def test_mean_hypothesis_cannot_be_dropped(self):
        V = 64
        positive_grid = sum(exp(-pi*(j/V)**2) for j in range(-500, 501))
        self.assertGreater(positive_grid, 63)
        # Supremum is one. A generic Schwartz family need not have O(1) grid sum.

    def test_prime_v_dft_exact(self):
        for p in (2, 3, 5, 7):
            for n, e, m in product(units(p), repeat=3):
                for k in range(-p, p+1):
                    lhs = []
                    for v in units(p):
                        center = F(ram(p, n*m+e*v))-F(mobius(p)*ram(p, m), phi(p))
                        lhs.append((F(k*v, p), F(mobius(p), p)*center))
                    rhs = [] if k % p == 0 else [
                        (F(-k*n*m*pow(e, -1, p), p), F(-1)),
                        (F(0), -F(1, p-1))]
                    self.assertTrue(roots_equal(lhs, rhs))

    def test_reciprocity_phase_exact_including_negative_k(self):
        for e, p in product(range(2, 20), (2, 3, 5, 7, 11)):
            if gcd(e, p) > 1:
                continue
            for k, n, m in product((-5, -1, 1, 4), (1, 3), (1, 2)):
                phase = -F(k*n*m*pow(e, -1, p), p)+F(k*n*m, e*p)
                target = F(k*n*m*pow(p, -1, e), e)
                self.assertEqual((phase-target) % 1, 0)

    def test_fixed_L_retains_joint_n_dependence(self):
        # A retained delta cutoff is F(|ep*y-nm|/L), not a function of y alone.
        e, p, y, m, L = 2, 3, 5, 4, 2
        arg = lambda n: F(e*p*y-n*m, L)
        self.assertNotEqual(arg(5), arg(6))
        self.assertEqual(arg(6)-arg(5), -F(m, L))


if __name__ == '__main__':
    unittest.main()
