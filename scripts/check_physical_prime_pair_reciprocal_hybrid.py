#!/usr/bin/env python3
"""Finite guards only: not a proof of stationary phase, LS, or the full gate."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt, ceil, sqrt
from pathlib import Path
import unittest

from check_physical_centered_conductor_split import roots_equal
from check_physical_large_gcd_type_columns import mobius


def root_map(terms):
    out = defaultdict(F)
    for phase, coefficient in terms:
        out[phase % 1] += coefficient
    return [(phase, a) for phase, a in out.items() if a]


def equal(left, right):
    return roots_equal(root_map(left), root_map(right))


def primitive_root(p):
    return next(g for g in range(1, p)
                if len({pow(g, j, p) for j in range(p-1)}) == p-1)


def physical_exponents(eta):
    return (F(7, 2)-F(5, 2)*eta, 2-eta, F(5, 2)-F(3, 2)*eta, F(1))


def packet_parts(e, q, component):
    old, np, principal, old_q, bad_e, bad_q, n_q = ([] for _ in range(7))
    for n, r, s in product(range(1, 36), (-7, -3, -1, 1, 3, 7),
                           (-5, -1, 1, 5)):
        if gcd(n, e) != 1:
            continue
        # Nonseparable rational real/imaginary weights, with original mu(n).
        numerator = n*r+s*e+q if component == 0 else n*s-r*q+e
        weight = F(mobius(n)*numerator, q*(n+1)*(abs(r)+1)*(abs(s)+1))
        raw = F(n*r*s*pow(e, -1, q), q)
        chirp = F(n*r*s, e*q)
        inv = F(-n*r*s*pow(q, -1, e), e)+chirp
        uq, ue, nq = gcd(r*s, q) == 1, gcd(r*s, e) == 1, n % q != 0
        if uq and nq:
            old += [(raw, weight), (F(0), weight/F(q-1))]
            old_q += [(F(0), weight/F(q-1))]
            if not ue:
                bad_e += [(raw, weight)]
        if ue:
            np += [(inv, weight), (chirp, weight/F(e-1))]
            principal += [(chirp, -weight/F(e-1))]
            if not uq:
                bad_q += [(raw, weight)]
            elif not nq:
                n_q += [(raw, weight)]
    return old, np, principal, old_q, bad_e, bad_q, n_q


class PrimePairReciprocalHybridTests(unittest.TestCase):
    def test_prime_double_dft_all_coordinates(self):
        for p in (3, 5, 7, 11):
            for lam, r, s in product(range(1, p), (-2, 0, 1, p),
                                     (-1, 0, 2, p)):
                lhs = []
                for u, v in product(range(1, p), repeat=2):
                    lhs += [(F(-lam*u*v+r*u+s*v, p), F(1)),
                            (F(r*u+s*v, p), F(1, p-1))]
                rhs = [] if r*s % p == 0 else [
                    (F(pow(lam, -1, p)*r*s, p), F(p)), (F(0), F(p, p-1))]
                self.assertTrue(equal(lhs, rhs), (p, lam, r, s))

    def test_two_poisson_normalization(self):
        for q, U, V in product((3, 5, 11), (F(1, 2), F(7)), (F(3), F(9))):
            self.assertEqual(F(1, q*q)*q*U*V, U*V/q)
            self.assertNotEqual(F(1, q*q)*q*U*V, U*V)

    def test_exact_reciprocity_both_signs(self):
        for e, q in ((3, 5), (5, 7), (7, 11), (11, 13)):
            for n, r, s in product(range(1, 16), (-3, -1, 1, 2), (-2, 1, 3)):
                left = F(n*r*s*pow(e, -1, q), q)
                right = F(-n*r*s*pow(q, -1, e), e)+F(n*r*s, e*q)
                self.assertEqual((left-right).denominator, 1)

    def test_full_nonprincipal_gauss_expansion(self):
        for e in (3, 5, 7, 11, 13):
            g = primitive_root(e)
            logs = {pow(g, j, e): j for j in range(e-1)}
            for x in range(1, e):
                rhs = [(F(0), -F(1, e-1))]
                for character in range(1, e-1):
                    for y in range(1, e):
                        rhs.append((F(y, e)+F(character*(logs[x]-logs[y]), e-1),
                                    F(1, e-1)))
                self.assertTrue(equal([(F(x, e), F(1))], rhs))

    def test_new_principal_is_not_zero(self):
        self.assertFalse(equal([(F(1, 5), F(1))],
                               [(F(1, 5), F(1)), (F(0), F(1, 4))]))

    def test_complete_complex_weighted_packet(self):
        for e, q, component in product((3, 5), (7, 11), (0, 1)):
            old, np, principal, old_q, bad_e, bad_q, n_q = packet_parts(e, q, component)
            rhs = np+principal+old_q+bad_e+[(x, -a) for x, a in n_q+bad_q]
            self.assertTrue(equal(old, rhs), (e, q, component))

    def test_omitted_errors_have_real_counterexamples(self):
        old, np, principal, old_q, bad_e, bad_q, n_q = packet_parts(3, 7, 0)
        full = np+principal+old_q+bad_e+[(x, -a) for x, a in n_q+bad_q]
        for terms in (principal, old_q, bad_e, bad_q, n_q):
            self.assertFalse(equal([], terms))
            self.assertFalse(equal(old, full+terms))

    def test_original_n_q_mask_exact_without_mobius_factorization(self):
        for q, end in product((3, 5, 7, 11), range(1, 81)):
            lhs = sum(mobius(n)*(n+1) for n in range(1, end+1) if n % q)
            rhs = sum(mobius(n)*(n+1) for n in range(1, end+1))
            rhs -= sum(mobius(q*j)*(q*j+1) for j in range(1, end//q+1))
            self.assertEqual(lhs, rhs)
            self.assertLessEqual(end//q, F(end, q))
        self.assertNotEqual(mobius(3*3), mobius(3)*mobius(3))

    def test_modulus_conjugation_not_linear_replacement(self):
        for a, b, c, d in product((1+2j, -2+1j, 3-4j), repeat=4):
            self.assertAlmostEqual(abs(a*b*c*d), abs(a*b*c.conjugate()*d.conjugate()))
        self.assertNotEqual((1+2j)*(3+4j), (1+2j)*(3+4j).conjugate())

    def test_coupled_q_mask_is_not_independent_product(self):
        q, rs = 3, (1, 3)
        coupled = sum(r for r in rs if gcd(q, r) == 1)
        self.assertNotEqual(coupled, sum(rs))

    def test_short_X_squared_cost_without_discarding_one(self):
        for E, R, K0, nu, theta in product((F(2), F(5)), (F(3), F(11)),
                (F(2), F(7)), (F(1), F(4), F(20)), (F(1, 100), F(1, 4), F(1), F(8))):
            X, K = nu*theta, K0*theta
            actual = R*K*(R+E**2*(1+X))*(K+E**2*(1+X))/(E*(1+X))
            natural = R**2*K0**2/(E*nu)+E*R**2*K0+E*R*K0**2+E**3*R*K0*nu
            self.assertLessEqual(actual, 2*max(theta, theta**2)*natural)
            expanded = R**2*K**2/(E*(1+X))+E*R**2*K+E*R*K**2+E**3*R*K*(1+X)
            self.assertEqual(actual, expanded)

    def test_chirp_and_product_scales(self):
        for R, E, Q, U, V in product((F(7), F(11)), (F(3), F(5)),
                                     (F(13),), (F(2), F(4)), (F(3), F(6))):
            D1, D2 = Q/U, Q/V
            self.assertEqual(R*D1*D2/(E*Q), R*Q/(E*U*V))
            self.assertEqual(Q*D1*D2, Q**3/(U*V))

    def test_four_cost_exponents_and_local_saving(self):
        for numerator in range(100, 126):
            self.assertEqual(max(physical_exponents(F(numerator, 100))), 1)
        self.assertEqual(physical_exponents(F(6, 5)), (F(1, 2), F(4, 5), F(7, 10), F(1)))
        self.assertEqual(F(11, 10)-max(physical_exponents(F(6, 5))), F(1, 10))

    def test_missing_stationary_factor_has_wrong_cost(self):
        self.assertEqual(max(x+F(1, 2) for x in physical_exponents(F(6, 5))), F(3, 2))

    def test_new_principal_remains_unpaid(self):
        self.assertEqual(F(7, 2)-2*F(6, 5), F(11, 10))
        self.assertGreater(F(7, 2)-2*F(6, 5), 1)

    def test_bad_dual_tail_exponents(self):
        for numerator in range(100, 126):
            eta = F(numerator, 100)
            self.assertLessEqual(F(13, 2)-7*eta, -F(1, 2))
            self.assertLess(-F(23, 2)+5*eta, 0)

    def test_divisor_growth_tail_and_time_margin(self):
        # Squared dyadic scales make sqrt(lambda) rational.
        for j in range(-12, 13):
            lam = F(4)**j
            root = F(2)**j
            weight = (root+lam)/(1+lam)**7
            bound = 2*root if j <= 0 else 2*lam**(-6)
            self.assertLessEqual(weight, bound)
        for j in range(13):
            self.assertEqual(F(2)**(-6*j)*F(2)**j, F(2)**(-5*j))

    def test_physical_support_prime_witness(self):
        e, q = 101, 1009
        S = R = e*q
        n = next(n for n in range(S+1, 2*S)
                 if all(n % d for d in range(2, isqrt(n)+1)))
        T, N = (8*S)**(1/3), 8*S
        H = L = S/sqrt(T)
        u = v = ceil(H/e)
        self.assertLess(2*e, q)
        self.assertEqual(gcd(n, e*q), 1)
        self.assertEqual(gcd(u*v, q), 1)
        self.assertLessEqual(n, N/4)
        self.assertLessEqual(e*q, N/4)
        self.assertTrue(H <= e*u <= 2*H and L <= e*v <= 2*L)
        x = 3*sqrt(T)/4
        y = (n*x+e*v)/(e*q)
        self.assertTrue(sqrt(T)/2 <= y <= 2*sqrt(T))

    def test_document_keeps_tail_masks_and_scope(self):
        text = (Path(__file__).resolve().parents[1]/'docs/research/'
                '2026-08-31-physical-prime-pair-reciprocal-hybrid.md').read_text()
        for required in ('不另插联合硬截断', 'O_q+B_e-B_n-B_q',
                         'K 并非对所有对偶块都为固定 T 幂',
                         'P_rec 不含已在 RH3 支付的 q-dual 掩码',
                         'EE*、EC*、CE*、CC*', '整个 C 的11/10瓶颈'):
            self.assertIn(required, text)
        self.assertIn('不证明 coupled-kernel gate', text)


if __name__ == '__main__':
    unittest.main()
