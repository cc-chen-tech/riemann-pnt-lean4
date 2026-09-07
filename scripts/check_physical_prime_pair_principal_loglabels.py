#!/usr/bin/env python3
"""Finite guards for LP candidate; none certifies analytic exponential sums."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import gcd
import unittest
from pathlib import Path

from check_physical_prime_pair_reciprocal_hybrid import equal, mobius, physical_exponents


def parts(e, q, component):
    p, full, bad_n, bad_dual = ([] for _ in range(4))
    for n, r, s in product(range(1, 28), (-6, -3, -1, 1, 2, 5), (-5, -1, 1, 3)):
        numerator = n*r+q*s+e if component == 0 else n*s-e*r+q
        w = -F(mobius(n)*mobius(e)*mobius(q)*numerator,
               q*(e-1)*(n+1)*(abs(r)+1)*(abs(s)+1))
        term = (F(n*r*s, e*q), w)
        full.append(term)
        if n % e == 0:
            bad_n.append(term)
        elif r*s % e == 0:
            bad_dual.append(term)
        else:
            p.append(term)
    return p, full, bad_n, bad_dual


def exponents(eta):
    return F(10, 3)-2*eta, 4-3*eta, F(13, 2)-8*eta, 3-2*eta


class PrincipalLogLabelTests(unittest.TestCase):
    def test_signed_complete_mask_subtraction(self):
        for e, q, component in product((3, 5), (7, 11), (0, 1)):
            p, full, bn, bd = parts(e, q, component)
            self.assertTrue(equal(p, full+[(x, -a) for x, a in bn+bd]))

    def test_bad_masks_are_not_zero(self):
        p, full, bn, bd = parts(3, 7, 0)
        self.assertFalse(equal(bn, []))
        self.assertFalse(equal(bd, []))
        self.assertFalse(equal(p, full))
        self.assertFalse(equal(p, full+[(x, -a) for x, a in bn]))
        self.assertFalse(equal(p, full+[(x, -a) for x, a in bd]))

    def test_overlap_counted_once_and_original_mobius(self):
        for e, n, r, s in product((3, 5), range(1, 21), range(1, 9), range(1, 9)):
            unit = int(n % e != 0 and r*s % e != 0)
            self.assertEqual(unit, 1-int(n % e == 0)-int(n % e != 0 and r*s % e == 0))
        self.assertNotEqual(mobius(3*3), mobius(3)*mobius(3))

    def test_n_multiple_count_has_no_extra_one(self):
        for end, e in product(range(1, 130), (3, 5, 7, 11)):
            self.assertEqual(sum(n % e == 0 for n in range(1, end+1)), end//e)
            self.assertLessEqual(end//e, F(end, e))

    def test_bad_n_full_physical_prefactor(self):
        for T, R, S, E, Q, U, V in product((F(3),), (F(13),), (F(17),),
                                          (F(5),), (F(19),), (F(2), F(4)), (F(3), F(6))):
            D1, D2 = Q/U, Q/V
            cost = T/(R*S)*(E*Q)*(R/E)*U*V/(Q*E)*D1*D2
            self.assertEqual(cost, T*Q*Q/(S*E))

    def test_logarithmic_chirp_identity_and_natural_scale(self):
        for R, E, Q, J1, J2, U, V in product((F(13),), (F(5),), (F(19),),
                (F(1, 2), F(3)), (F(1), F(7)), (F(2),), (F(4),)):
            D1, D2 = Q/U, Q/V
            nu = R*D1*D2/(E*Q)
            theta = (J1/D1)*(J2/D2)
            self.assertEqual(nu*theta, R*J1*J2/(E*Q))
            self.assertEqual(U*V*D1*D2, Q*Q)

    def test_small_dual_has_bounded_label_lengths(self):
        for a, b in product(range(-1, 9), repeat=2):
            J1, J2 = F(2)**a, F(2)**b
            X = J1*J2
            self.assertLessEqual(J1, 2*X)
            self.assertLessEqual(J2, 2*X)
            if X <= 1:
                self.assertLessEqual(J1, 2)
                self.assertLessEqual(J2, 2)

    def test_weighted_H4_and_original_derivative_budget(self):
        self.assertGreater(F(4), F(5, 2)+F(2, 3))
        self.assertLessEqual(12+12+4, 30)
        self.assertEqual(12-4, 8)
        self.assertLess(F(3), F(5, 2)+F(2, 3))

    def test_high_atom_shift_loss_is_paid(self):
        # Cubes/sixth powers make the claimed weight comparison rational.
        for x, j, w in product((1, 2, 4, 8), (1, 2, 3, 5), (1, 2, 4, 16)):
            X, J, omega = F(x)**6, F(j)**2, F(w)**3
            if J <= X and omega >= X:
                self.assertLessEqual(J, F(x)*j*w)

    def test_stationary_product_power_is_five_sixths(self):
        self.assertEqual(2*F(1, 6)+F(1, 2), F(5, 6))
        self.assertEqual(F(5, 6)-F(1, 2), F(1, 3))

    def test_common_eq_product_with_complex_coefficients(self):
        # Exact Gaussian-integer coefficient convolution; no extra e count.
        es, qs = (3, 5), (7, 11)
        coeff = defaultdict(complex)
        for e, q in product(es, qs):
            coeff[e*q] += complex(e, 1)*complex(1, -q)
        for z in (1j, -1, 1):
            left = sum(
                complex(e, 1)*complex(1, -q)*z**(e*q) for e, q in product(es, qs))
            self.assertEqual(left, sum(a*z**h for h, a in coeff.items()))
        self.assertEqual(len(coeff), len(es)*len(qs))

    def test_eq_two_column_energy_not_one_coefficient_per_pair_twice(self):
        for e, q in product((3, 5), (7, 11)):
            self.assertEqual(e*q, q*e)
        # Separation 2E<Q forbids an accidental swapped representation here.
        products = [e*q for e, q in product((3, 5), (13, 17))]
        self.assertEqual(len(set(products)), len(products))

    def test_infinite_dual_mean_ratio(self):
        for R, S, nu, theta in product((F(3), F(101)), (F(7), F(99)),
                (F(1), F(11)), (F(1, 100), F(1, 2), F(1), F(4), F(100))):
            ratio_sq = (R+nu*theta)*(S+nu*theta)/((R+nu)*(S+nu))
            self.assertLessEqual(ratio_sq, max(1, theta)**2)

    def test_large_small_dyadic_majorant_with_epsilon_growth(self):
        # theta^(1/3) + theta^(7/3), absorbs 2eps<=1.
        for a, b in product(range(-10, 11), repeat=2):
            l1, l2 = F(8)**a, F(8)**b
            t13 = F(2)**(a+b)
            weight = (t13+t13**7)/((1+l1)**8*(1+l2)**8)
            env1 = F(2)**a if a <= 0 else F(2)**(-17*a)
            env2 = F(2)**b if b <= 0 else F(2)**(-17*b)
            self.assertLessEqual(weight, 2*env1*env2)

    def test_mellin_outer_time_majorant(self):
        for j, X in product(range(15), (F(1), F(8), F(100))):
            W = F(2)**j*X
            self.assertEqual(X*W**(-3)*F(2)**j, X**(-2)*F(2)**(-2*j))

    def test_natural_exponent_and_mask_exponents(self):
        for eta in (F(1), F(7, 6), F(6, 5), F(5, 4)):
            main = 1+(5-2*eta)-3+F(1, 3)
            self.assertEqual(main, exponents(eta)[0])
            self.assertEqual(1+2*(3-eta)-3-eta, exponents(eta)[1])
            self.assertEqual(max(exponents(eta)), main)

    def test_whole_packet_threshold_and_no_double_saving(self):
        eta = F(6, 5)
        self.assertEqual(exponents(eta)[0], F(14, 15))
        self.assertEqual(F(11, 10)-exponents(eta)[0], F(1, 6))
        whole = max(max(exponents(eta)), *physical_exponents(eta), F(1))
        self.assertEqual(whole, 1)
        self.assertEqual(F(11, 10)-whole, F(1, 10))
        self.assertEqual(exponents(F(7, 6))[0], 1)
        self.assertGreater(exponents(F(23, 20))[0], 1)

    def test_remaining_nonzero_principal_is_bounded_not_vanishing(self):
        self.assertFalse(equal(parts(3, 7, 0)[0], []))


    def test_log_difference_second_derivative_scale(self):
        for J, x, h in product((F(2), F(8), F(32)), (F(1), F(3, 2), F(2)), (F(1), F(2))):
            j = J*x
            if h <= J:
                normalized = (1/j**2-1/(j+h)**2)/(h/J**3)
                self.assertGreaterEqual(normalized, F(1, 18))
                self.assertLessEqual(normalized, F(3))

    def test_difference_parameter_exact_three_terms(self):
        for a, b in product((2, 4, 8, 16), repeat=2):
            J, tau = F(a)**2, F(b)**6
            H = J/F(b)**2
            if J**3 <= tau**2 <= J**6:
                first = J**2/H
                second = F(b)**3*a*(a/F(b))
                third = F(a)**5/F(b)**3/(a/F(b))
                self.assertEqual(first, J*F(b)**2)
                self.assertEqual(second, first)
                self.assertEqual(third, J**2/F(b)**2)
                self.assertLessEqual(third, first)

    def test_document_keeps_complete_object_and_scope(self):
        text = (Path(__file__).resolve().parents[1]/'docs/research/'
                '2026-08-31-physical-prime-pair-principal-loglabels.md').read_text()
        for required in ('P=P_0-B_n-B_d', '12+12+4=28≤30', '普通 H³ 不能',
                         'Bₙ(old)', 'EE*、EC*、CE*、CC*', '7/6', '不是主导项自动消失',
                         '半范数', '合数 e/q', '不证明 coupled-kernel gate'):
            self.assertIn(required, text)


if __name__ == '__main__':
    unittest.main()
