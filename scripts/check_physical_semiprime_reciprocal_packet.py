#!/usr/bin/env python3
"""Finite semiprime guards, not analytic certification."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt, ceil, sqrt
import unittest
from pathlib import Path

from check_physical_centered_conductor_split import characters, roots_equal
from check_physical_large_gcd_type_columns import mobius, phi, units
from check_physical_squarefree_type_descent import divisors


def induced_exponents(eta):
    return F(7, 2)-F(9, 4)*eta, 2-F(5, 4)*eta, F(5, 2)-F(7, 4)*eta, 1-F(3, 4)*eta


def principal_terms(e, q, component, expanded=False, bad_extra_mask=False):
    result = []
    for n, r, s in product(range(1, 30), (-3, -1, 1, 5), (-2, 1, 3)):
        numerator = n*r+e*s+q if component == 0 else n*s-r*q+e
        w = F(numerator, q*phi(e)*(n+1)*(abs(r)+1)*(abs(s)+1))
        if not expanded:
            if gcd(n, e) == 1:
                result.append((F(n*r*s, e*q), w*mobius(q)*mobius(n)))
        else:
            for f in divisors(gcd(e, n)):
                a, m = e//f, n//f
                if bad_extra_mask and gcd(m, a) != 1:
                    continue
                result.append((F(m*r*s, a*q), w*mobius(f)*mobius(q)*mobius(f*m)))
    return result


class SemiprimeReciprocalTests(unittest.TestCase):
    def test_full_original_packet_signed_error_ledger(self):
        for e, q in ((6, 13), (15, 37)):
            old, new, oldq, bade, nq, badq = ([] for _ in range(6))
            for n, r, s in product(range(1, q+5), (-3, 1, 5, q), (-1, 2, 5)):
                if gcd(n, e) != 1:
                    continue
                w = F(mobius(e)*mobius(q)*mobius(n)*(n+r*e-s*q),
                      q*(n+1)*(abs(r)+1)*(abs(s)+1))
                raw = F(n*r*s*pow(e, -1, q), q)
                uq, ue, unq = gcd(r*s, q) == 1, gcd(r*s, e) == 1, n % q != 0
                if uq and unq:
                    old += [(raw, w), (F(0), w/F(q-1))]
                    oldq += [(F(0), w/F(q-1))]
                    if not ue:
                        bade.append((raw, w))
                if ue:
                    recip = F(-n*r*s*pow(q, -1, e), e)+F(n*r*s, e*q)
                    new.append((recip, w))
                    if not uq:
                        badq.append((raw, w))
                    elif not unq:
                        nq.append((raw, w))
            self.assertTrue(roots_equal(old, new+oldq+bade+[(x, -a) for x, a in nq+badq]))

    def test_all_characters_unique_three_nonprincipal_types(self):
        for p, r in ((2, 3), (3, 5), (3, 7), (5, 7), (5, 11)):
            e = p*r
            counts = defaultdict(int)
            for ell, _ in characters(e):
                counts[ell] += 1
            self.assertEqual(counts[1], 1)
            self.assertEqual(counts[p], p-2)
            self.assertEqual(counts[r], r-2)
            self.assertEqual(counts[e], (p-2)*(r-2))
            self.assertEqual(sum(counts.values()), phi(e))

    def test_complete_semiprime_gauss_expansion(self):
        for e in (6, 15, 21, 35):
            chars = characters(e)
            for x in units(e):
                rhs = [(F(0), F(mobius(e), phi(e)))]
                for ell, phases in chars:
                    if ell == 1:
                        continue
                    rhs.extend((F(y, e)-phases[y]+phases[x], F(1, phi(e))) for y in units(e))
                self.assertTrue(roots_equal([(F(x, e), F(1))], rhs))

    def test_induced_gauss_exact_cofactor_phase(self):
        for c, ell in ((2, 3), (3, 5), (5, 3), (5, 7)):
            e = c*ell
            for conductor, chi in characters(ell):
                if conductor != ell:
                    continue
                actual = [(F(y, e)-chi[y % ell], F(mobius(e))) for y in units(e)]
                expected = [(F(y, ell)-chi[y]-chi[c % ell], F(mobius(ell))) for y in units(ell)]
                self.assertTrue(roots_equal(actual, expected))

    def test_principal_sign_and_phi_are_not_prime_formula(self):
        for e in (6, 15, 21, 35):
            self.assertEqual(F(mobius(e)**2, phi(e)), F(1, phi(e)))
            self.assertNotEqual(F(mobius(e)**2, phi(e)), -F(mobius(e), e-1))

    def test_complete_n_e_ie_with_joint_complex_weights(self):
        for e, q, component in product((6, 15, 21), (23, 29), (0, 1)):
            self.assertTrue(roots_equal(principal_terms(e, q, component),
                                         principal_terms(e, q, component, expanded=True)))

    def test_no_extra_m_a_coprimality_after_ie(self):
        a = principal_terms(15, 23, 0)
        wrong = principal_terms(15, 23, 0, expanded=True, bad_extra_mask=True)
        self.assertFalse(roots_equal(a, wrong))

    def test_mu_fm_is_not_factored_without_masks(self):
        self.assertNotEqual(mobius(3*3), mobius(3)*mobius(3))
        for e, n in product((6, 15, 21, 35), range(1, 70)):
            actual = mobius(n) if gcd(e, n) == 1 else 0
            expanded = sum(mobius(f)*mobius(f*(n//f)) for f in divisors(gcd(e, n)))
            self.assertEqual(actual, expanded)

    def test_primitive_and_induced_are_not_the_same_layer(self):
        e = 15
        self.assertGreater(sum(ell == 3 for ell, _ in characters(e)), 0)
        self.assertGreater(sum(ell == e for ell, _ in characters(e)), 0)
        self.assertEqual(sum(ell == 2 for ell, _ in characters(6)), 0)

    def test_two_induced_orderings_each_represent_different_conductor(self):
        for p, r in ((3, 5), (5, 7)):
            pairs = {(p*r//ell, ell) for ell, _ in characters(p*r) if ell not in (1, p*r)}
            self.assertEqual(pairs, {(p, r), (r, p)})

    def test_common_IE_normalization_and_chirp(self):
        for f, m, a, q, r, s in product((1, 3, 5), (2, 7), (3, 11), (13,), (-2, 1), (-1, 3)):
            self.assertEqual(F(f*m*r*s, f*a*q), F(m*r*s, a*q))
            R, E = F(77), F(55)
            self.assertEqual(F(f*m, R), F(m)/(R/f))
            self.assertEqual(F(f*a, E), F(a)/(E/f))
            self.assertEqual((R/f)/(E/f), R/E)

    def test_fixed_cofactor_masks_remain_common(self):
        c = 3
        valid = [n for n in range(1, 20) if gcd(n, c) == 1]
        self.assertNotIn(3, valid)
        for ell in (5, 7):
            # The c mask is fixed; ell unit is separately provided by chi zero extension.
            combined = [n for n in valid if gcd(n, ell) == 1]
            self.assertEqual(combined, [n for n in range(1, 20) if gcd(n, c*ell) == 1])

    def test_complete_f_root_upper_bound(self):
        # Square the four positive terms without using numerical square roots.
        for R0, S0, X0, f in product((2, 4), (3, 5), (1, 2, 7), (1, 2, 5, 11)):
            R, S, X = F(R0*R0), F(S0*S0), F(X0*X0)
            # Choose f as square to make all root terms rational.
            f = F(f*f)
            lhs_sq = (R/f)*(S/f)*(R/f+X)*(S/f+X)
            fs = F(isqrt(f.numerator))
            upper = R*S/f**2+X0*(R*S0+S*R0)/(f*fs)+X*R0*S0/f
            self.assertLessEqual(lhs_sq, upper**2)

    def test_f_cost_harmonic_and_no_E_power(self):
        for n in (1, 4, 16, 64):
            s2 = sum(F(1, f*f) for f in range(1, n+1))
            self.assertLessEqual(s2, 2)
            harmonic = sum(F(1, f) for f in range(1, n+1))
            self.assertLessEqual(harmonic, 1+n.bit_length())

    def test_induced_four_exponents(self):
        self.assertEqual(induced_exponents(F(6, 5)), (F(4, 5), F(1, 2), F(2, 5), F(1, 10)))
        self.assertEqual(max(induced_exponents(F(7, 6))), F(7, 8))
        for eta in (F(7, 6), F(6, 5), F(5, 4)):
            self.assertLessEqual(max(induced_exponents(eta)), 1)

    def test_bad_e_sixteen_derivatives_and_threshold(self):
        self.assertLessEqual(16+2, 30)
        for eta in (F(7, 6), F(6, 5), F(5, 4)):
            raw = F(7, 2)-eta+16*(F(1, 2)-eta/2)
            self.assertEqual(raw, F(23, 2)-9*eta)
            self.assertLessEqual(raw, 1)
            self.assertEqual(raw-eta, F(23, 2)-10*eta)
        self.assertEqual(F(23, 2)-9*F(6, 5), F(7, 10))
        self.assertGreater(F(7, 2)-F(7, 6)+6*(F(1, 2)-F(7, 12)), 1)

    def test_principal_and_whole_saving_not_multiplied(self):
        eta = F(6, 5)
        principal = F(10, 3)-2*eta
        self.assertEqual(principal, F(14, 15))
        self.assertEqual(max(principal, *induced_exponents(eta), F(1)), 1)
        self.assertEqual(F(11, 10)-1, F(1, 10))

    def test_semiprime_support_is_new_not_prime(self):
        e, q, n = 101*103, 1000003, 1000033
        self.assertEqual(mobius(e), 1)
        self.assertEqual(len([d for d in divisors(e) if d > 1]), 3)
        self.assertGreater(q, 2*e)
        self.assertEqual(gcd(n, e*q), 1)


    def test_complete_original_semiprime_support(self):
        e, q = 11*13, 1009
        S = R = e*q
        n = next(n for n in range(S+1, 2*S)
                 if all(n % d for d in range(2, isqrt(n)+1)))
        T, N = (8*S)**(1/3), 8*S
        H = L = S/sqrt(T)
        u = v = ceil(H/e)
        self.assertEqual(mobius(e), 1)
        self.assertEqual(mobius(n), -1)
        self.assertLess(2*e, q)
        self.assertEqual(gcd(n, e*q), 1)
        self.assertEqual(gcd(u*v, q), 1)
        self.assertLessEqual(n, N/4)
        self.assertLessEqual(e*q, N/4)
        self.assertTrue(H <= e*u <= 2*H and L <= e*v <= 2*L)
        x = 3*sqrt(T)/4
        y = (n*x+e*v)/(e*q)
        self.assertTrue(sqrt(T)/2 <= y <= 2*sqrt(T))

    def test_document_scope_and_full_costs(self):
        text = (Path(__file__).resolve().parents[1]/'docs/research/'
                '2026-08-31-physical-semiprime-reciprocal-packet.md').read_text()
        for required in ('C_b', '=F+O_q+B_e-B_{nq}-B_{qd}',
                         '18≤30', '不因子化', 'R/f', 'S/f', 'log(2E)',
                         'EE*、EC*、CE*、CC*', '不覆盖不平衡半素数e',
                         '不证明完整 coupled-kernel gate', 'A₃₀'):
            self.assertIn(required, text)


if __name__ == '__main__':
    unittest.main()
