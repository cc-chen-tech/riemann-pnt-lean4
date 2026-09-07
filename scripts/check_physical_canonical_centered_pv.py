#!/usr/bin/env python3
"""Exact finite CP guards; not a proof of PV, LS, or the coupled gate."""
from fractions import Fraction as F
from itertools import product
from math import ceil, gcd, sqrt
import unittest

from check_physical_centered_conductor_split import characters, roots_equal
from check_physical_large_gcd_type_columns import mobius, phi
from check_physical_squarefree_type_descent import divisors
from check_physical_centered_pv_large_sieve import exponents as fp3_exponents


def balanced_exponents(eta, delta, z):
    eta, delta, z = map(F, (eta, delta, z))
    r = s = F(3)
    h = ell = F(5, 2)
    m, q, outer = delta - eta, 3 - delta, 1 - r - s
    return tuple(outer + term for term in (
        r + h + ell - eta - z / 2,
        r + (m + q + h + ell - eta) / 2,
        h + ell - eta + (q + r) / 2,
        (m + 3*q + r + h + ell - eta) / 2,
        m + eta + r + z / 2,
        m + r + eta / 2 + 3*z / 2,
        m + eta + r / 2 + 3*z / 2,
        m + (eta + r) / 2 + 5*z / 2,
    ))


def full_pv_exponents(eta, delta):
    return balanced_exponents(eta, delta, 3 - F(delta))[4:]


def cross_unit_mask(a0, b0, c, u, v):
    return int(gcd(u, b0*c) == gcd(v, a0*c) == 1)


class CanonicalCenteredPVTests(unittest.TestCase):
    def test_allocation_and_outer_cost_at_new_point(self):
        # Omitting a0/b0 rows or using Q=T^(3-eta) changes this vector.
        self.assertEqual(
            balanced_exponents(F(13, 10), F(3, 2), F(57, 40)),
            tuple(F(n, 80) for n in (79, 56, 76, 56, 17, 79, 11, 73)),
        )

    def test_full_pv_does_not_charge_absent_high_end(self):
        self.assertEqual(
            full_pv_exponents(F(1), F(2)),
            (F(1, 2), F(1), F(0), F(1, 2)),
        )

    def test_cross_masks_do_not_disappear_when_c_is_one(self):
        self.assertEqual(cross_unit_mask(2, 3, 1, 3, 1), 0)
        self.assertEqual(cross_unit_mask(2, 3, 1, 1, 2), 0)
        self.assertEqual(cross_unit_mask(2, 3, 1, 2, 3), 1)

    def test_complete_label_divisor_masks_with_signed_labels(self):
        for a0, b0, c in ((2, 3, 5), (5, 7, 6), (1, 3, 2), (2, 1, 1)):
            for u, v in product(range(-9, 10), repeat=2):
                if not u*v:
                    continue
                expanded = sum(
                    mobius(j)*mobius(k)
                    for j in divisors(b0*c) for k in divisors(a0*c)
                    if u % j == v % k == 0
                )
                self.assertEqual(expanded, cross_unit_mask(a0, b0, c, u, v))

    def test_overlapping_mask_divisors_are_required(self):
        # j=k=5 is necessary when both labels meet the c-prime.
        terms = [(j, k, mobius(j)*mobius(k))
                 for j in divisors(15) for k in divisors(10)
                 if 5 % j == 5 % k == 0]
        self.assertEqual(sum(t for _, _, t in terms), 0)
        self.assertEqual(sum(t for j, k, t in terms if gcd(j, k) == 1), -1)

    def test_mobius_full_ie_identity_all_f_not_just_f_one(self):
        for f, x, y in product(range(1, 13), repeat=3):
            lhs = mobius(f)*mobius(f*x)*mobius(f*y)
            rhs = mobius(f)*mobius(x)*mobius(y)*int(gcd(x*y, f) == 1)
            self.assertEqual(lhs, rhs)
        # Restoring (x,y)=1 after IE would change the e=n=2 coefficient.
        self.assertEqual(sum(mobius(f) for f in divisors(2)), 0)
        self.assertEqual(sum(mobius(f) for f in divisors(2)
                             if gcd(2//f, 2//f) == 1), -1)

    def test_joint_weight_complete_ie_with_canonical_cross_masks(self):
        for a0, b0, q0, q in ((2, 3, 1, 5), (3, 5, 2, 7), (1, 2, 3, 35),
                              (2, 3, 5, 1)):
            lhs, rhs = {}, {}
            for e, n, u, v in product(range(1, 13), range(1, 14),
                                      (-3, -1, 1, 2), (-2, -1, 1, 3)):
                if gcd(e*n, a0*b0*q0*q) > 1:
                    continue
                if not cross_unit_mask(a0, b0, q, u, v):
                    continue
                weight = F(e*n + u-v + e*v*v + 3*n*u, 31)
                phase = (-e*u*v*pow(n, -1, q)) % q if q > 1 else 0
                coeff = mobius(a0)*mobius(b0)*mobius(q)
                if gcd(e, n) == 1:
                    lhs[phase] = lhs.get(phase, F(0)) + coeff*mobius(e)*mobius(n)*weight
                for f in divisors(gcd(e, n)):
                    x, y = e//f, n//f
                    pulled = (-x*u*v*pow(y, -1, q)) % q if q > 1 else 0
                    self.assertEqual(pulled, phase)
                    sign = mobius(f)*mobius(x)*mobius(y)*int(gcd(x*y, f) == 1)
                    rhs[pulled] = rhs.get(pulled, F(0)) + coeff*sign*weight
            self.assertEqual({k:v for k,v in lhs.items() if v},
                             {k:v for k,v in rhs.items() if v})

    def test_primitive_columns_keep_a_b_and_c_unit_masks(self):
        for q in (6, 10, 15, 21, 30, 35):
            for ell, ambient in characters(q):
                if ell == 1:
                    continue
                c = q//ell
                small = {n % ell: z for n, z in ambient.items()}
                a0, b0, f, q0 = 11, 13, 17, 19
                for modulus in (f*q0*a0*b0, b0, a0):
                    actual = [(ambient[n % q], F(mobius(abs(n))*(n+2), 47))
                              for n in range(-15, 24) if n and gcd(n, modulus*q) == 1]
                    common = {n: F(mobius(abs(n))*(n+2), 47)
                              for n in range(-15, 24) if n and gcd(n, modulus*c) == 1}
                    induced = [(small[n % ell], w) for n, w in common.items()
                               if gcd(n, ell) == 1]
                    self.assertTrue(roots_equal(actual, induced), (q, ell, modulus))

    def test_new_divisor_cost_does_not_become_free(self):
        for a0, b0, c in ((2, 3, 5), (5, 7, 6), (1, 3, 10)):
            self.assertEqual(len(divisors(b0*c))*len(divisors(a0*c)),
                             len(divisors(a0))*len(divisors(b0))*len(divisors(c))**2)
            self.assertGreater(len(divisors(b0*c))*len(divisors(a0*c)),
                               len(divisors(c))**2)

    def test_five_actual_coordinates_have_no_allocation_loss(self):
        for a0, b0, f in product((1, 2, 5), (1, 3, 7), (1, 5, 17)):
            E, R, H, L, Q = map(F, (47, 131, 223, 227, 13))
            S = a0*b0*E*Q
            x, y, q, u, v = map(F, (3, 7, 11, -2, 5))
            X, Y, U, V = E/f, R/f, H/(a0*E), L/(b0*E)
            actual = (f*y/R, a0*b0*f*x*q/S, b0*f*x*v/L, a0*f*x*u/H)
            normalized = (y/Y, (a0*b0*E*Q/S)*(x/X)*(q/Q),
                          (x/X)*(v/V), (x/X)*(u/U))
            self.assertEqual(actual, normalized)

    def test_hard_shell_is_not_a_label_only_mask_after_ie(self):
        u = F(3, 4)
        self.assertEqual([int(1 <= x*u <= 2) for x in (F(1), F(3, 2))], [0, 1])
        # The new smooth packet retains this x/u coupling in the actual weight.
        for eE in (F(1), F(3, 2), F(199, 100)):
            self.assertGreaterEqual(F(1, 2)/eE, F(1, 4))
            self.assertLessEqual(F(2)/eE, F(2))

    def test_all_a_b_count_budgets_include_endpoint_one(self):
        for A0, B0 in product((1, 2, 4, 8, 16), repeat=2):
            pairs = tuple(product(range(A0, 2*A0), range(B0, 2*B0)))
            inv = sum(F(1, a*b) for a, b in pairs)
            self.assertLessEqual(inv, 1)
            self.assertEqual(len(pairs), A0*B0)
            # Cauchy: (sum 1/sqrt(ab))^2 <= (#pairs) sum 1/(ab).
            self.assertLessEqual(len(pairs)*inv, A0*B0)
        self.assertEqual(F(1, 1*1), 1)

    def test_all_f_powers_pay_harmonic_last_terms(self):
        E, R, H, L, a0, b0, Q = map(F, (47, 131, 223, 227, 2, 3, 13))
        K0 = H*L/(a0*b0*E)
        for f in range(1, 65):
            X, Y, K = E/f, R/f, K0/f
            self.assertEqual((Y*K)**2, (R*K0)**2/f**4)
            self.assertEqual(Q*Y*Y*K, Q*R*R*K0/f**3)
            self.assertEqual(Q*K*K*Y, Q*K0*K0*R/f**3)
            self.assertEqual(Q**3*Y*K, Q**3*R*K0/f**2)
            self.assertEqual(X*Y, E*R/f**2)
        self.assertGreater(sum(F(1, f) for f in range(1, 65)), 4)

    def test_fp3_specialization_matches_eight_frozen_terms(self):
        for eta in (F(4, 3), F(7, 5), F(3, 2), F(2)):
            z = F(5, 2)-3*eta/4
            self.assertEqual(balanced_exponents(eta, eta, z),
                             tuple(fp3_exponents(eta).values()))

    def test_new_polytope_interval_exact_rational_grid(self):
        for i in range(41):
            eta = F(14, 11) + F(i, 40)*(F(4, 3)-F(14, 11))
            lower, upper, z = 4-2*eta, (7*eta-6)/2, 4-2*eta
            for j in range(21):
                delta = lower + F(j, 20)*(upper-lower)
                self.assertTrue(eta <= delta <= 3)
                self.assertTrue(0 <= z <= 3-delta)
                self.assertLessEqual(max(balanced_exponents(eta, delta, z)), 1)

    def test_interval_endpoint_and_uncovered_allocation(self):
        self.assertEqual(balanced_exponents(F(14, 11), F(16, 11), F(16, 11)),
                         (F(1), F(8, 11), F(1), F(17, 22),
                          F(2, 11), F(1), F(3, 22), F(21, 22)))
        self.assertGreater(balanced_exponents(F(14, 11), F(14, 11), F(1))[2], 1)

    def test_full_pv_coverage_conditions_exact_grid(self):
        for i, j in product(range(31), repeat=2):
            eta, delta = F(i, 10), F(j, 10)
            if eta <= delta <= 3 and eta+delta >= 3 and eta+3*delta >= 6:
                self.assertLessEqual(max(full_pv_exponents(eta, delta)), 1)

    def test_centered_principal_and_trivial_count_are_distinct(self):
        eta, delta = F(13, 10), F(3, 2)
        best = max(balanced_exponents(eta, delta, F(57, 40)))
        principal, trivial = 3-eta, 6-delta-eta
        self.assertEqual((best, principal, trivial), (F(79, 80), F(17, 10), F(16, 5)))
        self.assertEqual(principal-best, F(57, 80))
        self.assertGreater(min(full_pv_exponents(1, 1)[1:2]), 1)
        self.assertGreater(balanced_exponents(1, 1, 1)[2], 1)

    def test_actual_integer_and_continuous_support_witness(self):
        # Exact integer/unit checks; continuous inequalities have wide margins.
        a0, b0, e, q = 2, 3, 8209, 32771
        factors = (a0, b0, e, q)
        self.assertTrue(all(mobius(x) != 0 for x in factors))
        self.assertTrue(all(gcd(x, y) == 1 for i,x in enumerate(factors) for y in factors[i+1:]))
        S = a0*b0*e*q
        n = next(S+k for k in range(1, 101) if gcd(S+k, S) == 1 and mobius(S+k))
        T = (8*S)**(1/3)
        H = S/sqrt(T)
        u = b0*ceil(H/(a0*e*b0))+1
        v = a0*ceil(H/(b0*e*a0))+1
        h, ell = a0*e*u, b0*e*v
        self.assertTrue(H <= h <= 2*H and H <= ell <= 2*H)
        self.assertEqual(cross_unit_mask(a0, b0, q, u, v), 1)
        self.assertEqual(gcd(S, gcd(h, ell)), e)
        self.assertEqual(gcd(S, h*ell), a0*b0*e)
        self.assertTrue(S < n < 2*S and n <= (8*S)/4)
        y = ((3*sqrt(T)/4)*n + ell)/S
        self.assertTrue(sqrt(T)/2 < y < 2*sqrt(T))


if __name__ == "__main__":
    unittest.main()
