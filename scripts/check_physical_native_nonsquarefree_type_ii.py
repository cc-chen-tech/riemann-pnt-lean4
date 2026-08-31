"""Exact finite guards for NS1--NS9, not proofs of analytic bounds.

Run with python -B scripts/check_physical_native_nonsquarefree_type_ii.py.
Only the frozen parent script supplies elementary arithmetic helpers.
No source writes, Lean, network, or temporary research-file imports.
"""
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt, prod
import unittest

import sympy as sp
from check_physical_native_principal_type_i import divisors, gamma, mu, phi, sigma


def square_sum(n, D, small):
    return sum(mu(nu) for nu in range(2, isqrt(n)+1)
               if n % (nu*nu) == 0 and (nu <= D if small else nu > D))


def quotient_l(B, nu):
    return nu*nu//gcd(nu*nu, B)


def square_unit_factor(A, w, n, B, nu, extra=False):
    L = quotient_l(B, nu)
    if n % (B*L) or gcd(B*L, A*w) != 1:
        return 0
    y, value = n//(B*L), 0
    for t in divisors(gcd(y, A)):
        z = y//t
        if gcd(z, w) != 1:
            continue
        if extra and gcd(z, t) != 1:
            continue
        value += mu(t)
    return value


def common_ie(n, w, g, extra=False):
    return sum(mu(f)**2*mu(w//f)*g*int(gcd(w//f, f) == 1)
               for f in divisors(gcd(n, w))
               if not extra or gcd(n//f, f) == 1)


def physical_exponents(beta, delta):
    return (F(-2, 5), beta-F(7, 5)+delta, F(-52, 5),
            F(11, 10)-delta/2, F(3, 5)-delta/2, F(3, 5))


class NativeNonsquarefreeChecks(unittest.TestCase):
    def test_complete_signed_square_split(self):
        for n in range(1, 501):
            for D in (1, 2, 3, 7, 20):
                self.assertEqual(1-mu(n)**2,
                                 -square_sum(n, D, True)-square_sum(n, D, False))

    def test_overlap_quotient_equivalence(self):
        for B in range(1, 61):
            for nu in range(1, 21):
                for m in range(1, 51):
                    self.assertEqual((B*m) % (nu*nu) == 0, m % quotient_l(B, nu) == 0)

    def test_nu_square_cannot_replace_overlap_quotient(self):
        self.assertEqual((quotient_l(4, 2), quotient_l(2, 2)), (1, 2))
        self.assertEqual((4*1) % 4, 0)
        self.assertNotEqual(1 % 4, 0)

    def test_complete_square_and_original_unit_IE(self):
        for A in (1, 2, 6, 15):
            for w in range(1, 21):
                if not mu(w) or gcd(A, w) != 1:
                    continue
                for B in range(1, 9):
                    for nu in range(2, 8):
                        if not mu(nu):
                            continue
                        for n in range(B, 91, B):
                            self.assertEqual(square_unit_factor(A, w, n, B, nu),
                                             int(n % (nu*nu) == 0 and gcd(n, A*w) == 1))

    def test_extra_z_t_mask_is_false(self):
        # L=1 for B=nu²; residual y=4 is not coprime to A=2.
        self.assertEqual(square_unit_factor(2, 3, 100, 25, 5), 0)
        self.assertNotEqual(square_unit_factor(2, 3, 100, 25, 5, True), 0)

    def test_exact_finite_Euler_cost_with_overlap(self):
        primes = (2, 3, 5, 7, 11)
        nus = [prod(p for p, bit in zip(primes, bits) if bit)
               for bits in product((0, 1), repeat=len(primes))]
        for B in range(1, 81):
            direct = sum((F(1, quotient_l(B, nu)) for nu in nus), F(0))
            expected = prod(1+F(gcd(p*p, B), p*p) for p in primes)
            self.assertEqual(direct, expected)
            self.assertLessEqual(direct, 2*len(divisors(B)))

    def test_squarefree_f_exact_divisibility(self):
        for f in range(1, 61):
            if not mu(f):
                continue
            for nu in range(1, 21):
                if not mu(nu):
                    continue
                modulus = nu*nu//gcd(nu, f)
                for x in range(1, 41):
                    self.assertEqual((f*x) % (nu*nu) == 0, x % modulus == 0)

    def test_squarefree_f_hypothesis_is_essential(self):
        self.assertEqual((4*1) % 4, 0)
        self.assertNotEqual(1 % (4//gcd(2, 4)), 0)

    def test_complete_tail_majorant_finite_prefix(self):
        for f in range(1, 61):
            if not mu(f):
                continue
            for D in (1, 2, 4, 9, 20):
                tail = sum((F(gcd(v, f), v*v) for v in range(D+1, 401)), F(0))
                self.assertLessEqual(tail, F(2*len(divisors(f)), D))

    def test_large_square_sparse_support_all_f(self):
        for f in range(1, 61):
            if not mu(f):
                continue
            for D in (1, 2, 4, 9, 20):
                for X in (2, 5, 11, 23):
                    support, majorant = set(), F(0)
                    for nu in range(D+1, isqrt(2*f*X)+1):
                        if mu(nu):
                            support.update(x for x in range(X, 2*X) if (f*x) % (nu*nu) == 0)
                            majorant += F(2*X*gcd(nu, f), nu*nu)
                    self.assertLessEqual(len(support), majorant)
                    self.assertLessEqual(len(support), F(4*X*len(divisors(f)), D))

    def test_literal_nonSF_Type_II_equals_Type_I(self):
        for U, V in ((1, 1), (2, 3), (4, 2), (5, 5)):
            for n in range(max(U, V)+1, 241):
                I, II = gamma(n, U, V), gamma(n, U, V, False)
                self.assertEqual(I*(1-mu(n)**2), II*(1-mu(n)**2))
        self.assertEqual((gamma(4, 1, 1), gamma(4, 1, 1, False), mu(4)), (1, 1, 0))

    def test_exact_paid_remainder_and_remaining_squarefree_column(self):
        for n in range(6, 301):
            I, II = gamma(n, 5, 5), gamma(n, 5, 5, False)
            for D in (1, 3, 7):
                small, large = -I*square_sum(n, D, True), -I*square_sum(n, D, False)
                self.assertEqual(mu(n), -I+small+large+mu(n)**2*II)

    def test_squarefree_long_factorization_only_after_mask(self):
        for n in range(2, 241):
            if not mu(n):
                continue
            ref = 0
            for b in divisors(n):
                for c in divisors(n//b):
                    m = n//(b*c)
                    self.assertEqual((gcd(b, c), gcd(b, m), gcd(c, m)), (1, 1, 1))
                    self.assertEqual(mu(b)*mu(c), mu(n)*mu(m))
                    if b > 3 and c > 3:
                        ref += mu(n)*mu(m)
            self.assertEqual(ref, gamma(n, 3, 3, False))
        self.assertNotEqual(mu(2)*mu(2), mu(4)*mu(1))

    def test_large_Gamma_full_common_column_IE(self):
        for U, V in ((1, 1), (2, 3), (4, 2)):
            for n in range(1, 81):
                for D in (1, 3, 6):
                    g = gamma(n, U, V)*square_sum(n, D, False)
                    for w in range(1, 31):
                        self.assertEqual(common_ie(n, w, g), mu(w)*g*int(gcd(n, w) == 1))

    def test_no_x_f_mask_on_actual_large_column(self):
        g = gamma(4, 1, 1)*square_sum(4, 1, False)
        self.assertEqual(g, -1)
        self.assertEqual(common_ie(4, 2, g), 0)
        self.assertNotEqual(common_ie(4, 2, g, True), 0)

    def test_full_signed_profile_reassembly_with_joint_complex_weight(self):
        for A, E in ((1, 2), (2, 6), (15, 30)):
            for D in (1, 3, 7):
                raw, split = {}, {}
                for w in range(1, 45):
                    if gcd(A, w) != 1:
                        continue
                    for n in range(4, 41):
                        if gcd(n, A*w) != 1:
                            continue
                        # Exact rational real/imag components are accumulated separately below.
                        weight = (F(n+2*w-3, n+w+1), F(2*n-w, n+3*w+1))
                        coeff = F(mu(A)*mu(w), A*A*w)*sigma(A, E, w)
                        I, II = gamma(n, 3, 3), gamma(n, 3, 3, False)
                        small, large = -I*square_sum(n, D, True), -I*square_sum(n, D, False)
                        for part in (0, 1):
                            key = (F(-n, w) % 1, part)
                            raw[key] = raw.get(key, F(0)) + coeff*weight[part]*II*(1-mu(n)**2)
                            split[key] = split.get(key, F(0)) + coeff*weight[part]*(small+large)
                self.assertEqual(dict(raw), dict(split))

    def test_sparse_energy_does_not_shorten_large_sieve_length(self):
        X, Y, D = F(100), F(7), F(4)
        correct_square = (X/D)*Y*(X+Y*Y)
        wrong_square = (X/D)*Y*(X/D+Y*Y)
        self.assertEqual(correct_square, F(26075))
        self.assertGreater(correct_square, wrong_square)

    def test_all_physical_costs_including_stationary_error(self):
        self.assertEqual(physical_exponents(F(2), F(1, 3)),
                         (F(-2, 5), F(14, 15), F(-52, 5), F(14, 15), F(13, 30), F(3, 5)))
        self.assertEqual(max(physical_exponents(F(2), F(1, 3))), F(14, 15))

    def test_larger_cutoff_endpoint_and_method_constraint(self):
        self.assertEqual(max(physical_exponents(F(11, 5), F(1, 5))), 1)
        self.assertGreater(max(physical_exponents(F(9, 4), F(1, 5))), 1)
        self.assertGreater(max(physical_exponents(F(11, 5), F(1, 6))), 1)

    def test_actual_nonsquarefree_native_support(self):
        T, h, d, c0, q, g = 72821, 101, 103, 71, 16338163, 3805463
        A, n = h*d, g*g
        w, s = c0*q, h*d*c0*q
        for p in (h, d, c0, q, g):
            self.assertTrue(sp.isprime(p))
        self.assertEqual(gcd(n, A*w), 1)
        self.assertEqual(gcd(A, w), 1)
        self.assertLess(s, n)
        self.assertLess(n, 2*s)
        self.assertLessEqual(2*max(n, s), T**3)
        self.assertLessEqual(T**6, (A*c0)**5)
        self.assertLess((A*c0)**5, 32*T**6)
        self.assertLess(h, F(n*h, s))
        self.assertLess(F(n*h, s), 2*h)
        self.assertGreater(6*F(n, w), T)
        self.assertLess(F(44, 7)*F(n, w), 2*T)
        self.assertLess(F(h*h, T), F(1, 2))
        self.assertGreater(g, T)
        self.assertEqual((gamma(n, T, T), gamma(n, T, T, False), mu(n)), (1, 1, 0))


if __name__ == '__main__':
    unittest.main(verbosity=2)
