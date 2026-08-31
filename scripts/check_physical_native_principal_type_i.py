"""Exact finite guards for NT1--NT11; not a proof of analytic tails.

Run with python -B scripts/check_physical_native_principal_type_i.py.
No repository writes, Lean invocation, or temporary research-file imports.
"""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, isqrt
import unittest

import sympy as sp


@lru_cache(None)
def divisors(n):
    low = [d for d in range(1, isqrt(n) + 1) if n % d == 0]
    return tuple(low + [n // d for d in reversed(low) if d * d != n])


@lru_cache(None)
def mu(n):
    if n == 1:
        return 1
    for p in range(2, isqrt(n) + 1):
        if n % p == 0:
            return 0 if (n // p) % p == 0 else -mu(n // p)
    return -1


@lru_cache(None)
def phi(n):
    return sum(gcd(k, n) == 1 for k in range(1, n + 1))


@lru_cache(None)
def gamma(n, U, V, short=True):
    return sum(mu(b)*mu(c) for b in divisors(n) for c in divisors(n//b)
               if (b <= U and c <= V if short else b > U and c > V))


def unit_factor(A, w, n, B, extra=None):
    if n % B or gcd(B, A*w) != 1:
        return 0
    m, value = n//B, 0
    for t in divisors(gcd(m, A)):
        z = m//t
        if gcd(z, w) != 1:
            continue
        if extra == 'z-t' and gcd(z, t) != 1:
            continue
        if extra == 'z-A/t' and gcd(z, A//t) != 1:
            continue
        value += mu(t)
    return value


def ram(q, L):
    return sum(d*mu(q//d) for d in divisors(gcd(q, abs(L))))


def sigma(A, E, w):
    return sum((F(mu(c0), c0*phi(c0)) for c0 in divisors(w)
                if E <= A*c0 < 2*E and w//c0 > 1), F(0))


def atom(h, n, w):
    # A genuinely joint rational weight; no separability assumption in reassembly.
    return F((h + 2*n + 3*w) % 11 - 5, 1 + h + n + w)


def full_sum(A, E, U, V, nmax, wmax, representation):
    acc = defaultdict(F)
    for w in range(1, wmax+1):
        if gcd(A, w) != 1:
            continue
        for n in range(1, nmax+1):
            if representation == 'raw':
                coeff = sum((F(mu(q)*gamma(n, U, V), (A*c0)**2*q*phi(c0))
                             for c0 in divisors(w) for q in (w//c0,)
                             if E <= A*c0 < 2*E and q > 1 and mu(c0)
                             and gcd(c0, q) == 1 and gcd(n, A*w) == 1), F(0))
            else:
                g = (sum(mu(b)*mu(c)*unit_factor(A, w, n, b*c)
                         for b in range(1, U+1) for c in range(1, V+1))
                     if representation == 'type'
                     else gamma(n, U, V)*int(gcd(n, A*w) == 1))
                coeff = F(g*mu(w), A*A*w)*sigma(A, E, w)
            for h in divisors(A):
                acc[F(-n, w) % 1] += mu(A)*coeff*atom(h, n, w)
    return {k: v for k, v in acc.items() if v}


def physical_exponents(eta, beta, J=12):
    C, R, W = eta-1, F(3), F(2)
    return (R-1-W-2*C, beta-1-2*C, R-1-2*C-J, R-2*eta)


class NativeTypeIChecks(unittest.TestCase):
    def test_type_identity_including_boundary(self):
        for U in range(1, 9):
            for V in range(1, 9):
                for n in range(1, 241):
                    boundary = (mu(n) if n <= U else 0) + (mu(n) if n <= V else 0)
                    self.assertEqual(mu(n), boundary - gamma(n, U, V)
                                     + gamma(n, U, V, False))

    def test_non_squarefree_parts_cannot_be_deleted(self):
        self.assertEqual((mu(4), gamma(4, 1, 1), gamma(4, 1, 1, False)), (0, 1, 1))

    def test_b_c_overlap_is_allowed(self):
        wrong = sum(mu(b)*mu(c) for b in divisors(4) for c in divisors(4//b)
                    if b <= 2 and c <= 2 and gcd(b, c) == 1)
        self.assertEqual(gamma(4, 2, 2), 0)
        self.assertEqual(wrong, -1)

    def test_no_mobius_on_unsigned_quotient(self):
        self.assertEqual(gamma(4, 1, 1), 1)
        self.assertNotEqual(gamma(4, 1, 1), mu(4))

    def test_full_unit_IE(self):
        for A in (1, 2, 6, 15, 35):
            for w in range(1, 31):
                if not mu(w) or gcd(A, w) != 1:
                    continue
                for B in range(1, 16):
                    for n in range(B, 90, B):
                        self.assertEqual(unit_factor(A, w, n, B), int(gcd(n, A*w) == 1))

    def test_no_residual_z_t_unit(self):
        self.assertEqual(unit_factor(2, 3, 4, 1), 0)
        self.assertNotEqual(unit_factor(2, 3, 4, 1, 'z-t'), 0)

    def test_no_residual_z_A_over_t_unit(self):
        self.assertEqual(unit_factor(2, 3, 4, 1), 0)
        self.assertNotEqual(unit_factor(2, 3, 4, 1, 'z-A/t'), 0)

    def test_signed_profile_and_q_one_exclusion(self):
        self.assertEqual(mu(15)*sigma(1, 3, 15), F(-13, 60))
        self.assertEqual(sigma(1, 15, 15), 0)  # q'=1 is not this projection.

    def test_original_profile_and_full_type_reassembly(self):
        for A in (1, 2, 6, 15):
            for C in (1, 3, 5):
                for U, V in ((1, 1), (2, 3), (3, 2)):
                    raw = full_sum(A, A*C, U, V, 19, 35, 'raw')
                    self.assertEqual(raw, full_sum(A, A*C, U, V, 19, 35, 'profile'))
                    self.assertEqual(raw, full_sum(A, A*C, U, V, 19, 35, 'type'))
        self.assertTrue(full_sum(1, 3, 2, 3, 19, 35, 'raw'))

    def test_exact_cyclotomic_shifted_DFT(self):
        x = sp.Symbol('x')
        for w in range(2, 32):
            cyclo = sp.Poly(sp.cyclotomic_poly(w, x), x, domain=sp.QQ)
            for a in (1, 2, 3, 7):
                for j in (0, 1, 2, a, a+1):
                    polynomial = sum(x**(((j-a)*r) % w) for r in range(w)
                                     if gcd(r, w) == 1) - ram(w, j-a)
                    self.assertTrue(sp.rem(sp.Poly(polynomial, x, domain=sp.QQ), cyclo).is_zero)

    def test_mean_uses_the_original_unit(self):
        self.assertEqual(ram(6, -1), mu(6))
        self.assertNotEqual(ram(6, -2), mu(6))

    def test_general_frequency_gcd_average(self):
        for W in range(1, 45):
            for L in range(-120, 121):
                if L == 0:
                    continue
                actual = sum(gcd(w, L) for w in range(W, 2*W))
                exact = sum(phi(d)*((2*W-1)//d - (W-1)//d) for d in divisors(abs(L)))
                self.assertEqual(actual, exact)
                self.assertLessEqual(actual, 2*W*len(divisors(abs(L))))

    def test_zero_difference_must_be_separate(self):
        self.assertEqual(ram(30, 0), 8)
        self.assertGreater(sum(gcd(w, 0) for w in range(20, 40)), 2*20)

    def test_special_frequency_is_R_over_w_even_for_short_Z(self):
        for B in (1, 7, 1000, 10**8):
            for t in (1, 2, 7, 30):
                R, W = F(10**6), F(10**4)
                a, Z = B*t, R/(B*t)
                self.assertEqual(a*Z/W, 100)
                for u in (F(1, 2), F(1), F(3, 2)):
                    self.assertEqual(B*t*(Z*u)/R, u)

    def test_stationary_normalization_includes_both_jacobians(self):
        for A in (6, 15, 35):
            for c0 in (1, 2, 7):
                for q in (2, 3, 11):
                    ep, w = A*c0, c0*q
                    self.assertEqual(F(1, ep*ep*q*phi(c0)),
                                     F(1, A*A*w)*F(1, c0*phi(c0)))
        u, v, beta, T = sp.symbols('u v beta T', real=True)
        transformed = T*(v + beta*(sp.exp(u)-1)/u)*u - T*beta*sp.exp(u)
        self.assertEqual(sp.simplify(transformed - (T*u*v-T*beta)), 0)

    def test_Gamma_common_column_IE_has_no_x_f_mask(self):
        for U, V in ((1, 1), (2, 3), (4, 2)):
            for n in range(1, 50):
                for w in range(1, 40):
                    rhs = sum(mu(f)**2*mu(w//f)*gamma(n, U, V)*int(gcd(w//f, f) == 1)
                              for f in divisors(gcd(n, w)))
                    self.assertEqual(gamma(n, U, V)*mu(w)*int(gcd(n, w) == 1), rhs)
        wrong = sum(mu(f)**2*mu(2//f)*gamma(4, 1, 1)*int(gcd(2//f, f) == 1)
                    *int(gcd(4//f, f) == 1) for f in divisors(2))
        self.assertNotEqual(wrong, 0)

    def test_physical_main_and_stationary_error(self):
        self.assertEqual(physical_exponents(F(6, 5), 2),
                         (F(-2, 5), F(3, 5), F(-52, 5), F(3, 5)))

    def test_largest_product_cutoff_and_unpaid_beyond(self):
        self.assertEqual(max(physical_exponents(F(6, 5), F(12, 5))), 1)
        self.assertGreater(max(physical_exponents(F(6, 5), F(5, 2))), 1)

    def test_native_internal_support_fixture(self):
        h, d, c0, q, n = 101, 103, 71, 16338163, 20112632646541
        A, T = h*d, 72821
        ep, w = A*c0, c0*q
        s, M, K = ep*q, h, h
        for p in (h, d, c0, q, n):
            self.assertTrue(sp.isprime(p))
        self.assertEqual(gcd(n, A*w), 1)
        self.assertEqual(gcd(A, w), 1)
        self.assertLessEqual(T**6, ep**5)
        self.assertLess(ep**5, 32*T**6)
        self.assertLessEqual(2*max(n, s), T**3)
        self.assertLess(s, n)
        self.assertLess(n, 2*s)
        self.assertLess(K, F(n*h, s))
        self.assertLess(F(n*h, s), 2*K)
        self.assertGreater(6*F(n, w), T)  # 3 < pi
        self.assertLess(F(44, 7)*F(n, w), 2*T)  # pi < 22/7
        self.assertLess(F(M*K, T), F(1, 2))
        self.assertLess(T, n)
        # n is prime > U=V=T: only b=c=1 contributes to Gamma_I.
        self.assertEqual(gamma(n, T, T), 1)
        self.assertEqual(gamma(n, T, T, False), 0)


if __name__ == '__main__':
    unittest.main(verbosity=2)
