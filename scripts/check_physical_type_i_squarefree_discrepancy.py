#!/usr/bin/env python3
"""Finite TIQ guards, not a proof of Weil, Poisson, or the signed gate."""
from fractions import Fraction as F
from collections import defaultdict
from itertools import product
from math import ceil, gcd, isqrt, sqrt
import unittest

from check_physical_large_gcd_type_columns import mobius, phi
from check_physical_squarefree_type_descent import divisors
from check_physical_centered_conductor_split import roots_equal


def error_exponent(eta, delta, beta=0, chi=0):
    eta, delta, beta, chi = map(F, (eta, delta, beta, chi))
    r = s = F(3)
    h = ell = F(5, 2)
    m, q = delta - eta, 3 - delta
    return 1 + h + ell + 2*q + m/2 + 3*beta/2 - chi/2 - 3*r/2 - s - eta


def transformed_unit_mask(a, t, B, A, q, z):
    return (gcd(q, A) == gcd(B, A*q) == gcd(a*t, A*B*q) ==
            gcd(a, t) == gcd(z, q) == 1)


def _add_kernel(output, q, phase, coefficient):
    output[phase % q] += coefficient
    output[0] -= coefficient * F(mobius(q), phi(q))


def _weight(e, n, u, v):
    return F((3*e+2*n+u*v)**2, (1+e*n)**2)


class TypeISquarefreeDiscrepancyTests(unittest.TestCase):
    def test_complete_allocation_error_at_small_overlap(self):
        self.assertEqual(error_exponent(F(6, 5), F(6, 5)), F(9, 10))
        self.assertEqual(error_exponent(F(7, 6), F(7, 6)), F(1))
        self.assertEqual(error_exponent(F(6, 5), F(6, 5), F(1, 30)), F(19, 20))

    def test_z_may_share_a_or_t(self):
        self.assertTrue(transformed_unit_mask(2, 3, 25, 7, 11, 6))

    def test_original_q_A_unit_condition_is_not_optional(self):
        self.assertIs(transformed_unit_mask(2, 3, 25, 7, 7, 6), False)

    def test_outer_q0_cost_and_canonical_count_are_retained(self):
        self.assertEqual(error_exponent(F(1), F(3, 2)), F(3, 4))
        self.assertEqual(error_exponent(F(1), F(3, 2), 0, F(1, 5)), F(13, 20))
        self.assertEqual(error_exponent(F(1), F(1)), F(3, 2))

    def test_original_two_cutoff_identity_with_full_endpoints(self):
        for n in range(1, 101):
            for U, V in ((1, 1), (2, 3), (4, 2), (5, 5)):
                short = long = 0
                for b in divisors(n):
                    for c in divisors(n//b):
                        term = mobius(b)*mobius(c)
                        if b <= U and c <= V:
                            short += term
                        if b > U and c > V:
                            long += term
                boundary = mobius(n)*(int(n <= U)+int(n <= V))
                self.assertEqual(mobius(n), -short+long+boundary)

    def test_square_factor_in_bc_and_unsigned_m_are_required(self):
        # n=4,U=V=1: the I term (b,c,m)=(1,1,4) cancels II (2,2,1).
        short = -1
        long = mobius(2)*mobius(2)
        self.assertEqual(short+long, mobius(4))
        self.assertNotEqual(0+long, mobius(4))
        self.assertNotEqual(short+0, mobius(4))

    def test_unique_split_of_each_mask_divisor(self):
        for A, e in ((6, 35), (10, 21), (1, 30), (7, 1)):
            pairs = [(w, t) for w in divisors(A) for t in divisors(e)]
            self.assertEqual(sorted(w*t for w, t in pairs), divisors(A*e))
            for m in range(1, 80):
                total = sum(mobius(w)*mobius(t) for w, t in pairs if m % (w*t) == 0)
                self.assertEqual(total, int(gcd(m, A*e) == 1))

    def test_squarefree_sign_fusion_including_zero_cases(self):
        for a, t in product(range(1, 24), repeat=2):
            rhs = mobius(a)*mobius(t)**2*int(gcd(a, t) == 1)
            self.assertEqual(mobius(a*t)*mobius(t), rhs)

    def test_complete_signed_type_i_reindex_with_joint_weights(self):
        fixtures = (
            (1, 1, 1, 5, 4, 18, 2, 3), (1, 1, 1, 6, 5, 20, -1, 5),
            (2, 3, 1, 5, 5, 30, 1, 1), (2, 1, 3, 5, 4, 22, 1, -1),
            (1, 1, 1, 1, 4, 18, 2, 3), (1, 1, 1, 30, 7, 40, 1, 7),
            (3, 5, 2, 7, 11, 48, 2, 2), (1, 1, 1, 7, 9, 28, 2, -3),
        )
        corrupted = overlapping = 0
        for a0, b0, q0, q, E, R, u, v in fixtures:
            A = q0*a0*b0
            for U, V in ((1, 1), (2, 3), (3, 3), (4, 2)):
                direct, joined, bad = (defaultdict(F) for _ in range(3))
                for e in range(E, 2*E):
                    if not mobius(e) or gcd(e, A*q) != 1:
                        continue
                    for b, c in product(range(1, U+1), range(1, V+1)):
                        B = b*c
                        if gcd(B, A*e*q) != 1:
                            continue
                        coefficient = -mobius(a0)*mobius(b0)*mobius(b)*mobius(c)*mobius(e)*mobius(q)
                        for n in range(R, 2*R):
                            if n % B or gcd(n//B, A*e*q) != 1:
                                continue
                            _add_kernel(direct, q, -e*u*v*pow(n, -1, q),
                                        coefficient*_weight(e, n, u, v))
                for a in range(1, 2*E):
                    for b, c in product(range(1, U+1), range(1, V+1)):
                        B = b*c
                        for w in divisors(A):
                            coefficient = -mobius(a0)*mobius(b0)*mobius(b)*mobius(c)*mobius(a)*mobius(q)*mobius(w)
                            if not coefficient:
                                continue
                            for t in range(1, 2*E):
                                e = a*t
                                if not E <= e < 2*E or not mobius(t):
                                    continue
                                for n in range(R, 2*R):
                                    if n % (B*t*w):
                                        continue
                                    z = n//(B*t*w)
                                    if not transformed_unit_mask(a, t, B, A, q, z):
                                        continue
                                    amount = coefficient*_weight(e, n, u, v)
                                    phase = -a*u*v*pow(B*w*z, -1, q)
                                    _add_kernel(joined, q, phase, amount)
                                    if gcd(z, a*t) == 1:
                                        _add_kernel(bad, q, phase, amount)
                                    overlapping += int(gcd(b, c) > 1)
                keys = set(direct) | set(joined) | set(bad)
                self.assertTrue(all(direct[k] == joined[k] for k in keys))
                corrupted += int(any(direct[k] != bad[k] for k in keys))
        self.assertEqual(corrupted, 16)
        self.assertGreater(overlapping, 0)

    def test_modular_inverse_phase_has_no_remaining_t(self):
        for q in (2, 5, 6, 15, 30):
            for a, t, B, w, z in ((2, 7, 9, 11, 13), (1, 7, 4, 1, 11), (7, 11, 4, 7, 13)):
                if gcd(a*t*B*w*z, q) != 1:
                    continue
                for u, v in ((1, 1), (2, -3), (-1, 5)):
                    left = -a*t*u*v*pow(B*t*w*z, -1, q)
                    right = -a*u*v*pow(B*w*z, -1, q)
                    self.assertEqual((left-right) % q, 0)

    def test_squarefree_unit_floor_identity(self):
        for J in (1, 6, 15, 30, 77):
            for height in (F(1, 2), F(3, 2), F(17, 3), F(31), F(101, 2)):
                n = height.numerator//height.denominator
                direct = sum(mobius(t)**2 for t in range(1, n+1) if gcd(t, J) == 1)
                expanded = sum(mobius(d)*sum(1 for m in range(1, n//(d*d)+1) if gcd(m, J) == 1)
                               for d in range(1, isqrt(n)+1) if gcd(d, J) == 1)
                self.assertEqual(direct, expanded)

    def test_half_open_t_shell_endpoints_are_not_doubled(self):
        for Y in (F(1, 2), F(1), F(3, 2), F(5, 3), F(7, 2)):
            actual = [t for t in range(1, ceil(2*Y)+1) if Y <= t < 2*Y]
            self.assertEqual(actual, list(range(ceil(Y), ceil(2*Y))))
        self.assertEqual([t for t in range(1, 3) if F(1, 2) <= t < 1], [])

    def test_physical_coordinates_have_uniform_two_variable_scaling(self):
        for a0, b0, E, R, q, B, w, a, u, v in (
            (2, 3, 10, 90, 7, 5, 2, 3, 4, -5),
            (1, 1, 21, 120, 11, 4, 1, 7, -2, 3),
        ):
            S, H, L = a0*b0*E*q, a0*E*abs(u), b0*E*abs(v)
            Y, Z = F(E, a), F(R*a, B*w*E)
            for xi, zz in product((F(1), F(3, 2), F(7, 4)), repeat=2):
                t, z = Y*xi, Z*zz
                actual = (B*t*w*z/R, a0*b0*a*t*q/S, b0*a*t*v/L, a0*a*t*u/H)
                expected = (xi*zz, F(a0*b0*E*q, S)*xi, F(b0*E*v, L)*xi, F(a0*E*u, H)*xi)
                self.assertEqual(actual, expected)

    def test_centered_full_fourier_zero_for_all_squarefree_moduli(self):
        for q in (1, 2, 3, 5, 6, 7, 10, 15, 21, 30):
            for lam in range(q):
                if gcd(lam, q) != 1:
                    continue
                terms = [(F(lam*pow(z, -1, q), q), F(1))
                         for z in range(q) if gcd(z, q) == 1]
                self.assertTrue(roots_equal(terms, [(F(0), F(mobius(q)))]))

    def test_nonunit_fourier_frequencies_must_not_be_dropped(self):
        q, lam, k = 6, 1, 2
        terms = []
        for z in range(q):
            if gcd(z, q) == 1:
                terms += [(F(lam*pow(z, -1, q)+k*z, q), F(1)),
                          (F(k*z, q), -F(mobius(q), phi(q)))]
        self.assertFalse(roots_equal(terms, []))

    def test_q_one_centered_kernel_is_exact_zero(self):
        result = defaultdict(F)
        _add_kernel(result, 1, 0, F(17, 5))
        self.assertEqual(dict(result), {0: F(0)})

    def test_small_critical_scale_sum_needs_no_integer_one(self):
        for critical in (F(1, 100), F(1, 4), F(1), F(4), F(25)):
            total = sum(a**(-.5)*min(1., float(critical/a)**3) for a in range(1, 5001))
            self.assertLessEqual(total, 4*sqrt(float(critical)))
        self.assertLess(float(F(1, 100)**3), sqrt(.01))

    def test_all_frequency_tail_uses_integral_majorant(self):
        for ratio, K in product((F(1, 8), F(1, 2), F(1), F(4)), (1, 3, 10)):
            tail = sum((1/(1+k*ratio)**4 for k in range(K+1, K+200)), F(0))
            self.assertLessEqual(tail, 1/(3*ratio*(1+K*ratio)**3))

    def test_allocation_divisor_and_label_counting(self):
        for A in (1, 6, 30, 105):
            self.assertLessEqual(sum(sqrt(w) for w in divisors(A)), len(divisors(A))*sqrt(A))
        for L0 in (F(1, 4), F(1, 2), F(3, 4), F(1), F(7, 2)):
            count = sum(1 for u in range(-8, 9) if 0 < abs(u) <= 2*L0)
            if L0 < F(1, 2):
                self.assertEqual(count, 0)
            else:
                self.assertLessEqual(count, 4*L0)

    def test_density_depends_on_the_shared_prime_set(self):
        # After dividing out 1/zeta(2), c(6)=1/2 but c(30)=5/12.
        self.assertEqual(F(2, 3)*F(3, 4), F(1, 2))
        self.assertEqual(F(2, 3)*F(3, 4)*F(5, 6), F(5, 12))
        self.assertNotEqual(F(1, 2), F(5, 12))

    def test_error_success_does_not_pay_the_mean_or_type_ii(self):
        eta = delta = F(6, 5)
        mean_budget = F(9, 2)-eta-F(3, 2)*delta
        self.assertEqual(mean_budget, F(3, 2))
        self.assertLess(error_exponent(eta, delta), 1)
        self.assertGreater(mean_budget, 1)

    def test_actual_original_type_i_support_is_nonempty(self):
        e, q = 101, 1009
        S = R = e*q
        T = (8*S)**(1/3)
        H = L = S/sqrt(T)
        u = v = ceil(H/e)
        # Bertrand prime selection is only the existence mechanism; find a small witness.
        def prime(n):
            return n >= 2 and all(n % p for p in range(2, isqrt(n)+1))
        n = next(n for n in range(S+1, 2*S) if prime(n))
        self.assertEqual(gcd(n, e*q), 1)
        self.assertEqual(gcd(u*v, q), 1)
        self.assertTrue(H <= e*u <= 2*H and L <= e*v <= 2*L)
        x = 3*sqrt(T)/4
        y = (x*n+e*v)/S
        self.assertTrue(sqrt(T)/2 <= y <= 2*sqrt(T))
        self.assertTrue(n <= 8*S/4)
        self.assertTrue(R/2 > 2)  # U_c=V_c=2 boundary absent; b=c=1 allowed.


if __name__ == "__main__":
    unittest.main()
