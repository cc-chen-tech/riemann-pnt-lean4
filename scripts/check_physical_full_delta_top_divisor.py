"""Exact finite guards for TD1--TD15, not an analytic proof certificate.

The analytic logarithmic exponent pair, original AFE derivative bounds,
mean-value estimate and infinite tails require the companion paper proof.
Run: python -B scripts/check_physical_full_delta_top_divisor.py
"""
from fractions import Fraction as F
from itertools import product
from math import gcd
import unittest
from check_physical_large_gcd_type_columns import mobius, phi, units
from check_physical_squarefree_type_descent import divisors
from check_physical_centered_conductor_split import characters, roots_equal


def ram(q, r):
    return sum(d*mobius(q//d) for d in divisors(gcd(q, r)))


def A(pair):
    k, ell = pair
    return k/(2*k+2), (k+ell+1)/(2*k+2)


def conductor_exponents(eta, z):
    kappa, lam = F(1, 62), F(57, 62)
    delta = 1+kappa-lam
    base = F(7, 2)-2*eta
    return ((F(1), 2-eta, F(5, 2)-F(3, 2)*eta, base-z/2),
            (base+kappa+delta*(1-eta)+(F(3, 2)+2*delta)*z,
             base-1+F(3, 2)*z))


class FullDeltaTopDivisorChecks(unittest.TestCase):
    def test_h_removal_including_nonunit_m(self):
        for e, m, r, n, q in product(range(1, 35), range(1, 13), range(-4, 5), (3, 7), (5, 11)):
            if not mobius(e):
                continue
            h = gcd(e, m)
            a, z = e//h, m//h
            self.assertEqual(F(ram(a, r), phi(a)), F(ram(e, m*r), phi(e)))
            self.assertEqual(h**4*a**3*n*q*z, e**3*n*q*m)
            self.assertEqual(F(q*a, n*z), F(q*e, n*m))

    def test_all_divisor_euler_with_q1_subtraction(self):
        for s, m, r in product((1, 2, 3, 6, 10, 15, 30, 42, 70, 105), range(1, 18), range(-8, 9)):
            direct = sum((F(ram(e, m*r), e*phi(e)) for e in divisors(s) if gcd(m, s//e) == 1), F(0))
            rhs = F(1)
            for p in divisors(s):
                if p == 1 or any(p % d == 0 for d in range(2, p)):
                    continue
                rhs *= F(1, p) if m % p == 0 else (1+F(1, p) if r % p == 0 else 1-F(1, p*(p-1)))
            self.assertEqual(direct, rhs)
            q_above_one = sum((F(ram(e, m*r), e*phi(e)) for e in divisors(s)
                              if e < s and gcd(m, s//e) == 1), F(0))
            self.assertEqual(q_above_one, rhs-F(ram(s, m*r), s*phi(s)))

    def test_stationary_d_phase_cancels(self):
        for q, d, b, n, z, r0, t in product((F(1), F(3)), repeat=7):
            # Suppress the common positive constant 2*pi, which cancels identically.
            ystar = t/(d*r0)
            self.assertEqual(q*d*b/(n*z)*ystar, q*b*t/(n*z*r0))

    def test_explicit_pairs_and_whole_principal_threshold(self):
        pair = F(1, 2), F(1, 2)
        for _ in range(3):
            pair = A(pair)
        self.assertEqual(pair, (F(1, 30), F(13, 15)))
        k, ell = pair
        delta = 1+k-ell
        eta = (F(5, 2)+k+delta)/(2+delta)
        self.assertEqual(eta, F(81, 65))
        self.assertEqual(F(5, 4)-eta, F(1, 260))
        pair = A(pair)
        self.assertEqual(pair, (F(1, 62), F(57, 62)))
        k, ell = pair
        self.assertEqual(F(11, 10)+k-(1+k-ell)/5, F(34, 31))

    def test_eta_six_fifths_endpoint_condition(self):
        for k, ell in product((F(0), F(1, 62), F(1, 30), F(1, 6)), (F(1, 2), F(5, 6), F(57, 62))):
            delta = 1+k-ell
            exponent = F(11, 10)+k-delta/5
            self.assertEqual(exponent-1, (4*k+ell-F(1, 2))/5)

    def test_induced_character_full_dft_exact(self):
        count = 0
        for ell, c in product((1, 3, 5, 7, 15), (1, 2, 3, 5, 6)):
            if gcd(ell, c) != 1:
                continue
            for cond, ch in characters(ell):
                if cond != ell:
                    continue
                a = ell*c
                for k in range(-2, a+2):
                    left = [(F(k*w, a)-ch[w % ell], F(1)) for w in units(a)]
                    right = ([(F(x, ell)-ch[x % ell]+ch[k % ell]-ch[c % ell], F(ram(c, k)))
                              for x in units(ell)] if gcd(k, ell) == 1 else [])
                    self.assertTrue(roots_equal(left, right), (ell, c, k))
                    count += 1
        print('exact_induced_DFT_cases', count)

    def test_unit_ie_scalar_resummation(self):
        for c, k in product((1, 2, 3, 6, 10, 15, 30), range(-28, 29)):
            self.assertEqual(sum((F(mobius(j), j) for j in divisors(c) if k % (c//j) == 0), F(0)),
                             F(ram(c, k), c))

    def test_induced_outer_mobius_ramanujan_fusion(self):
        for ell, c, k in product((1, 2, 3, 5, 6, 15), (1, 2, 3, 5, 6, 10, 30), range(-20, 21)):
            if k == 0 or gcd(c, ell) > 1:
                continue
            d = gcd(c, k)
            b = c//d
            original = F(mobius(c*ell)*ram(c, k), phi(c*ell))
            descended = F(mobius(ell)*mobius(d), phi(ell)*phi(b))
            self.assertEqual(original, descended)
            self.assertEqual(gcd(b, k), 1)

    def test_character_f_j_cancellation_after_three_ie(self):
        count = 0
        for ell in (3, 5, 7):
            for cond, ch in characters(ell):
                if cond != ell:
                    continue
                for f, j, l, C, X, Y, z, r0 in product((1, 2), repeat=8):
                    if gcd(f*j*l*C*X*Y*z*r0, ell) > 1:
                        continue
                    n, q, b = f*j*X, l*j*Y, f*l*C
                    original = ch[(n*z*r0) % ell]-ch[(q*b) % ell]
                    separated = ch[(X*z*r0) % ell]-ch[(l*l*C*Y) % ell]
                    self.assertEqual((original-separated) % 1, 0)
                    count += 1
        print('exact_character_three_IE_phases', count)

    def test_low_and_high_joint_exponents(self):
        eta, z = F(687, 550), F(1, 275)
        k, ell = F(1, 62), F(57, 62)
        delta = 1+k-ell
        baseline = F(7, 2)-2*eta
        self.assertEqual(5-4*eta, z)
        low = baseline+k+delta*(1-eta)+(F(3, 2)+2*delta)*z
        self.assertEqual(low, 1)
        self.assertEqual(baseline-z/2, 1)
        self.assertLess(baseline-1+F(3, 2)*z, 1)
        self.assertLess(2-eta, 1)
        self.assertLess(F(5, 2)-F(3, 2)*eta, 1)
        self.assertEqual(F(5, 4)-eta, F(1, 1100))

    def test_entire_stated_eta_interval_not_six_fifths(self):
        for i in range(101):
            eta = F(687, 550)+F(i, 110000)
            z = 5-4*eta
            high, low = conductor_exponents(eta, z)
            self.assertGreaterEqual(z, 0)
            self.assertLessEqual(max(high+low), 1)
        high, low = conductor_exponents(F(6, 5), F(1, 5))
        self.assertGreater(max(high+low), 1)
        high, low = conductor_exponents(F(687, 550), F(1, 275))
        self.assertEqual(high, (F(1), F(413, 550), F(689, 1100), F(1)))
        self.assertEqual(low, (F(1), F(2, 275)))

    def test_full_delta_profile_core_prefactor(self):
        for R, S, M, nratio, sratio, mratio, yratio in product((F(1), F(2)), repeat=7):
            K = M*R/S
            n, s, m, y = R*nratio, S*sratio, M*mratio, K*yratio
            physical_square = (R*S*M)**2/(n*s*s*s*m*y)
            self.assertEqual(physical_square, 1/(nratio*sratio**3*mratio*yratio))

    def test_all_characters_restore_top_congruence_without_overlap(self):
        count = 0
        for a in (1, 2, 3, 5, 6, 10, 15, 30):
            chars = characters(a)
            for cutoff in (F(2), F(3), F(7, 2), F(5), F(9)):
                low = [(ell, ch) for ell, ch in chars if ell < cutoff]
                high = [(ell, ch) for ell, ch in chars if ell >= cutoff]
                self.assertEqual(len(low)+len(high), phi(a))
                for x, y in product(units(a), repeat=2):
                    terms = [(ch[x]-ch[y], F(1, phi(a))) for _, ch in low+high]
                    expected = [(F(0), F(int((x-y) % a == 0)))]
                    self.assertTrue(roots_equal(terms, expected), (a, cutoff, x, y))
                    count += 1
        print('exact_low_high_character_reassembly', count)


if __name__ == '__main__':
    unittest.main()
