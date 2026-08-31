"""Exact finite guards for LQ1--LQ10, not analytic proofs.

Run with python -B scripts/check_physical_native_type_ii_large_quotient.py.
The frozen NT script supplies elementary arithmetic helpers only.
No source edits, Lean, network, or temporary research-file imports.
"""
from fractions import Fraction as F
from math import gcd
import unittest
import sympy as sp
from check_physical_native_principal_type_i import divisors, gamma, mu, sigma


def quotient_ie(A, w, l, m, extra_z=False):
    if gcd(A, w) != 1 or gcd(l, A*w) != 1:
        return 0
    ans = 0
    for alpha in divisors(A):
        for delta in divisors(w):
            if m % (alpha*delta):
                continue
            z, y = m//(alpha*delta), w//delta
            if gcd(y, A*delta) != 1:
                continue
            if extra_z and gcd(z, alpha*delta) != 1:
                continue
            ans += mu(alpha)*mu(delta)**2*mu(y)
    return ans


def common_mean_ie(l, y, extra_x=False):
    return sum(mu(r)**2*mu(y//r)*int(gcd(y//r, r) == 1)
               for r in divisors(gcd(l, y))
               if not extra_x or gcd(l//r, r) == 1)


def add(root, phase, factor, weight):
    for part in (0, 1):
        key = (phase % 1, part)
        root[key] = root.get(key, F(0)) + factor*weight[part]


def clean(root):
    return {key: val for key, val in root.items() if val}


def exponents(lam, J=12):
    return (F(19, 15)-lam/2, F(1, 10), F(3, 5), F(13, 5)-J)


class LargeQuotientChecks(unittest.TestCase):
    def test_original_unmasked_type_identity(self):
        for U, V in ((1, 1), (2, 3), (4, 4)):
            for n in range(max(U, V)+1, 181):
                self.assertEqual(mu(n), -gamma(n, U, V)+gamma(n, U, V, False))
        self.assertEqual(mu(2)*mu(2), 1)  # bc may be non-squarefree.
        self.assertEqual(mu(4), 0)       # the unsigned quotient may be non-squarefree.

    def test_whole_nonSF_identity_does_not_restrict_to_m_packet(self):
        # n=4, U=V=1: I has m=4 and II has m=1.
        n, U, V = 4, 1, 1
        def packet(short):
            return sum(mu(b)*mu(c) for b in divisors(n) for c in divisors(n//b)
                       if (b <= U and c <= V if short else b > U and c > V)
                       and n//(b*c) == 1)
        self.assertEqual((gamma(n, U, V), gamma(n, U, V, False)), (1, 1))
        self.assertEqual((packet(True), packet(False)), (0, 1))

    def test_full_quotient_unit_IE(self):
        for A in (1, 2, 6, 15, 35):
            for w in range(1, 32):
                for l in range(1, 13):
                    for m in range(1, 26):
                        expected = mu(w)*int(gcd(A, w) == 1 and gcd(l*m, A*w) == 1)
                        self.assertEqual(quotient_ie(A, w, l, m), expected)

    def test_extra_z_unit_is_false(self):
        self.assertEqual(quotient_ie(2, 3, 1, 4), 0)
        self.assertNotEqual(quotient_ie(2, 3, 1, 4, True), 0)

    def test_exact_phase_and_original_reciprocal_weight(self):
        for alpha in (1, 2, 3, 5):
            for delta in range(1, 8):
                for l, z, y in ((3, 4, 7), (4, 6, 5), (5, 2, 9)):
                    n, w = l*alpha*delta*z, delta*y
                    self.assertEqual(F(n, w), F(alpha*l*z, y))
                    self.assertEqual(F(1, w), F(1, delta*y))
        self.assertNotEqual(F(1, 2*3), F(1, 3))

    def test_signed_mobius_fusion(self):
        for A in (1, 2, 6, 15):
            for w in range(1, 71):
                if gcd(A, w) != 1:
                    continue
                for alpha in divisors(A):
                    for delta in divisors(w):
                        self.assertEqual(mu(w)*mu(alpha)*mu(delta),
                                         mu(alpha)*mu(delta)**2*mu(w//delta)
                                         *int(gcd(w//delta, delta) == 1))

    def test_full_joint_complex_weighted_root_reassembly(self):
        for A, E in ((1, 2), (2, 6), (15, 30)):
            raw, ie = {}, {}
            for w in range(2, 43):
                if gcd(A, w) != 1:
                    continue
                for b in range(2, 7):
                    for c in range(2, 7):
                        l = b*c
                        for m in range(2, 11):
                            n = l*m
                            weight = (F(n+m*w+1, n+w+3), F(b*c*c+w*m, n+2*w+1))
                            pref = F(mu(A)*mu(b)*mu(c), A*A*w)*sigma(A, E, w)
                            add(raw, F(-n, w), pref*mu(w)*int(gcd(n, A*w) == 1), weight)
                            if gcd(l, A*w) != 1:
                                continue
                            for alpha in divisors(A):
                                for delta in divisors(w):
                                    if m % (alpha*delta):
                                        continue
                                    z, y = m//(alpha*delta), w//delta
                                    factor = mu(alpha)*mu(delta)**2*mu(y)*int(gcd(y, A*delta) == 1)
                                    add(ie, F(-alpha*l*z, y), pref*factor, weight)
            self.assertEqual(clean(raw), clean(ie))

    def test_all_r_coprime_mean_reassembly(self):
        for l in range(1, 101):
            for y in range(1, 71):
                self.assertEqual(common_mean_ie(l, y), mu(y)*int(gcd(l, y) == 1))

    def test_r_IE_does_not_make_x_squarefree_or_unit(self):
        self.assertEqual(common_mean_ie(4, 2), 0)
        self.assertNotEqual(common_mean_ie(4, 2, True), 0)
        self.assertEqual(F(2*4, 2*3), F(4, 3))

    def test_common_bc_coefficients_after_r(self):
        for A, delta in ((1, 2), (6, 5), (15, 7)):
            coeff = {}
            for b in range(2, 12):
                for c in range(3, 14):
                    if gcd(b*c, A*delta) == 1:
                        coeff[b*c] = coeff.get(b*c, 0)+mu(b)*mu(c)*(b-2)*(c+3)
            for y in range(1, 31):
                raw = mu(y)*sum(v for l, v in coeff.items() if gcd(l, y) == 1)
                reduced = sum(v*common_mean_ie(l, y) for l, v in coeff.items())
                self.assertEqual(raw, reduced)

    def test_mv_square_expansion_all_three_powers(self):
        for T in (2, 5, 13):
            for L in (T, 3*T, 7*T):
                for Y in (T, 2*T, 9*T):
                    for r in range(1, min(L, Y)+1):
                        x, v = F(L, r), F(Y, r)
                        self.assertEqual((T+x)*x*(T+v)*v,
                                         F((L*Y)**2, r**4)
                                         +F(T*L*Y*(L+Y), r**3)
                                         +F(T*T*L*Y, r**2))

    def test_positive_support_count_has_no_extra_one(self):
        for X in (F(1, 4), F(1, 2), F(1), F(7, 3), F(11)):
            for r in range(1, 42):
                actual = sum(X <= r*k < 2*X for k in range(1, 100))
                self.assertLessEqual(actual, 2*X/r)

    def test_normalized_length_and_phase_relations(self):
        for T in (16, 81, 256):
            R, W = T**3, T**2
            for M in (1, 3, 7, 11):
                L = F(R, M)
                for alpha in (1, 2, 3):
                    for delta in range(1, 2*M//alpha+1):
                        Z, Y = F(M, alpha*delta), F(W, delta)
                        self.assertEqual(alpha*L*Z/Y, T)
                        self.assertGreaterEqual(Y, F(W, 2*M))

    def test_all_alpha_delta_powers_and_outer(self):
        T, R, W, C, M = F(64), F(64**3), F(64**2), F(3), F(16)
        L = R/M
        for alpha in (1, 4, 9):
            for delta in (1, 4, 9):
                # Squared leading factors avoid numerical square roots.
                left2 = (F(1, T*W)*C**-2*L*(W/delta))**2 * T**-1 * (M/(alpha*delta))
                right2 = (R*C**-2)**2/(T**3*M*alpha*delta**3)
                self.assertEqual(left2, right2)
                lower2 = (F(1, T*W)*C**-2*L*(W/delta)*M/(T*alpha*delta))**2/T
                self.assertEqual(lower2, R**2/(T**5*C**4*alpha**2*delta**4))
                tail = F(1, T*W)*C**-2*L*(W/delta)*(M/(alpha*delta))*T**(1-12)
                self.assertEqual(tail, R*C**-2*T**-12/(alpha*delta*delta))

    def test_exponent_pair_normalization_is_not_tk_zl(self):
        kappa, ell = F(1, 6), F(2, 3)
        self.assertEqual(ell-kappa, F(1, 2))
        self.assertEqual(F(3)-F(2, 5)+kappa-F(3, 2), F(19, 15))

    def test_physical_threshold_comparison_and_unpaid_nearby(self):
        self.assertEqual(exponents(F(8, 15)), (F(1), F(1, 10), F(3, 5), F(-47, 5)))
        lam = F(17, 30)
        self.assertEqual(max(exponents(lam)), F(59, 60))
        self.assertEqual(max(F(8, 5)-lam, F(3, 5)), F(31, 30))
        self.assertEqual(F(31, 30)-F(59, 60), F(1, 20))
        self.assertGreater(max(exponents(F(1, 2))), 1)

    def test_generic_mellin_moment_alone_has_no_saving(self):
        for X in (F(2), F(11), F(123)):
            for Y in (F(2), F(5), F(31)):
                theta = X/Y
                self.assertEqual((theta+X)*(theta+Y)/(theta*(X+Y*Y)), 1+1/Y)

    def test_actual_native_original_II_support_in_new_band(self):
        T, h, d, c0, q = 72821, 101, 103, 71, 16338163
        b, c, m = 154459, 154487, 607
        A, w, n = h*d, c0*q, b*c*m
        s = A*w
        for p in (h, d, c0, q, b, c, m):
            self.assertTrue(sp.isprime(p))
        self.assertEqual(gcd(n, A*w), 1)
        self.assertEqual(gcd(A, w), 1)
        self.assertLess(s, n)
        self.assertLess(n, 2*s)
        self.assertLessEqual(2*max(n, s), T**3)
        self.assertLessEqual(T**6, (A*c0)**5)
        self.assertLess((A*c0)**5, 32*T**6)
        self.assertGreater(6*F(n, w), T)
        self.assertLess(F(44, 7)*F(n, w), 2*T)
        self.assertLess(h, F(n*h, s))
        self.assertLess(F(n*h, s), 2*h)
        self.assertGreater(min(b, c), T)
        self.assertGreater(m**15, T**8)
        self.assertLess(m**5, T**3)
        self.assertEqual(mu(b)*mu(c), 1)


if __name__ == '__main__':
    unittest.main(verbosity=2)
