#!/usr/bin/env python3
"""Exact finite guards, not proofs of exponent-pair, mean-value or tail bounds."""

from fractions import Fraction as F
from itertools import product
from math import gcd, lcm
import unittest

from check_physical_large_gcd_type_columns import mobius, phi
from check_physical_squarefree_type_descent import divisors


def ram(q, r):
    return sum(d*mobius(q//d) for d in divisors(gcd(q, r)))


def ie(b, n, q, D0, Dn, Dq, forbidden=None):
    """Evaluate RP8, allowing a deliberately wrong mask for negative guards."""
    result = F(0)
    for f in divisors(gcd(b, n)):
        for ell in divisors(gcd(b//f, q)):
            if gcd(f, ell) > 1 or b % (f*ell):
                continue
            c = b//(f*ell)
            if not mobius(f)**2*mobius(ell)**2*mobius(c)**2:
                continue
            if gcd(f*ell*c, D0) > 1 or gcd(c, f*ell) > 1:
                continue
            for j in divisors(gcd(n//f, q//ell)):
                X, Y = n//(f*j), q//(ell*j)
                if gcd(j, f*ell*lcm(Dn, Dq)) > 1:
                    continue
                if gcd(X, j*f*ell*Dn) > 1 or gcd(Y, j*f*ell*Dq) > 1:
                    continue
                if forbidden and gcd(c, {'j': j, 'X': X, 'Y': Y}[forbidden]) > 1:
                    continue
                result += F(mobius(f)**2*mobius(ell)**2*mobius(c)**2
                            *mobius(j)*mobius(X)*mobius(Y), phi(f)*phi(ell)*phi(c))
    return result


class ReciprocalPrincipalChecks(unittest.TestCase):
    def test_complete_three_ie_exact(self):
        count = 0
        for b, n, q in product(range(1, 35), range(1, 24), range(1, 24)):
            if not mobius(b):
                continue
            for D0, Dn, Dq in ((1, 1, 1), (6, 2, 6), (30, 6, 30)):
                expected = F(mobius(b)**2*mobius(n)*mobius(q), phi(b))
                if (gcd(b, D0) > 1 or gcd(n, Dn) > 1 or gcd(q, Dq) > 1
                        or gcd(b, n*q) > 1 or gcd(n, q) > 1):
                    expected = F(0)
                self.assertEqual(ie(b, n, q, D0, Dn, Dq), expected, (b, n, q, D0))
                count += 1
        print('exact_three_IE_cases', count)

    def test_c_j_must_not_be_made_coprime(self):
        self.assertEqual(ie(2, 2, 2, 1, 1, 1), 0)
        self.assertNotEqual(ie(2, 2, 2, 1, 1, 1, 'j'), 0)

    def test_c_X_must_not_be_made_coprime(self):
        self.assertEqual(ie(2, 2, 1, 1, 1, 1), 0)
        self.assertNotEqual(ie(2, 2, 1, 1, 1, 1, 'X'), 0)

    def test_c_Y_must_not_be_made_coprime(self):
        self.assertEqual(ie(2, 1, 2, 1, 1, 1), 0)
        self.assertNotEqual(ie(2, 1, 2, 1, 1, 1, 'Y'), 0)

    def test_j_coefficient_is_signed(self):
        # For b=1,n=q=2, j=1 contributes +1 and j=2 contributes -1.
        self.assertEqual(ie(1, 2, 2, 1, 1, 1), 0)
        self.assertEqual(mobius(1)*mobius(2)**2+abs(mobius(2))*mobius(1)**2, 2)

    def test_full_ie_with_joint_rational_complex_weight(self):
        for D0, Dn, Dq in ((1, 1, 1), (6, 2, 6), (30, 6, 30)):
            for component in (0, 1):
                direct = expanded = F(0)
                for b, n, q in product(range(1, 15), repeat=3):
                    weight = (F(b*n+q, 7+b*q) if component == 0
                              else F(b*q-n*n, 11+b*n*q))
                    if (gcd(b, D0*n*q) == gcd(n, Dn*q) == gcd(q, Dq) == 1):
                        direct += weight*F(mobius(b)**2*mobius(n)*mobius(q), phi(b))
                    expanded += weight*ie(b, n, q, D0, Dn, Dq)
                self.assertEqual(expanded, direct)

    def test_phi_factorization_and_time_phase(self):
        for d, f, ell, c, j, X, Y, z in product((1, 2, 3), repeat=8):
            if gcd(f, ell) > 1 or gcd(c, f*ell) > 1:
                continue
            b = f*ell*c
            self.assertEqual(phi(b), phi(f)*phi(ell)*phi(c))
            a, n, q = d*b, f*j*X, ell*j*Y
            self.assertEqual(F(q*a, n*z), F(d*ell*ell*c*Y, X*z))

    def test_full_principal_prefactor_squared(self):
        for h, a, n, q, z, w in product(range(1, 5), repeat=6):
            # Original 2q/[sqrt(nhaq)*(haq)] times (hz*w/a)^(-1/2)/phi(a).
            before = F(4*q*q, n*h*a*q*(h*a*q)**2)*F(a, h*z*w)/phi(a)**2
            after = F(4, h**4*a*a*phi(a)**2*n*q*z*w)
            self.assertEqual(before, after)

    def test_reciprocal_gcd_and_ramanujan_ratio(self):
        for e, m, r in product(range(1, 60), range(1, 24), range(-15, 16)):
            if not mobius(e):
                continue
            h = gcd(e, m)
            a = e//h
            d = gcd(a, r)
            b = a//d
            self.assertEqual(h*d, gcd(e, m*r))
            self.assertEqual(F(mobius(a)*ram(a, r), phi(a)), F(mobius(d), phi(b)))
            self.assertEqual(F(ram(e, m*r), phi(e)), F(ram(a, r), phi(a)))

    def test_scalar_and_baseline_squared(self):
        for R, Q, E, M, K, T, h, d in product((F(1), F(3)), repeat=8):
            A, Z, D = E/h, M/h, T/K
            coefficient2 = K/T*Z*Z*(D/d)**2/(h**4*A**3*R*Q*Z)
            self.assertEqual(coefficient2*(R*Q)**2, R*Q*M/K*T/E**3/(h*d)**2)

    def test_log_exponent_pair_band_ledger(self):
        eta = F(6, 5)
        baseline = F(7, 2)-2*eta
        self.assertEqual(baseline, F(11, 10))
        first = lambda gamma: baseline+F(1, 6)+(F(gamma)-eta)/2
        self.assertEqual(first(F(2, 3)), 1)
        self.assertEqual(baseline-1, F(1, 10))
        self.assertEqual(first(1), F(7, 6))  # The whole band is NOT paid.
        k, ell = F(1, 2), F(1, 2)
        self.assertEqual((k/(2*k+2), (k+ell+1)/(2*k+2)), (F(1, 6), F(2, 3)))

    def test_no_deleted_delta_on_original_unit_support(self):
        for n, q, z, w in product(range(1, 15), repeat=4):
            if q > 1 and gcd(n*z, q) == 1:
                self.assertNotEqual(q*w, n*z)

    def test_full_square_divisor_identity(self):
        for n in range(1, 450):
            self.assertEqual(sum(mobius(u) for u in divisors(n) if n % (u*u) == 0),
                             mobius(n)**2)
        # Truncating at u=1 would spuriously keep c=4.
        self.assertNotEqual(mobius(1), mobius(4)**2)

    def test_reciprocal_phi_convolution(self):
        for n in range(1, 220):
            self.assertEqual(sum((F(mobius(s)**2, phi(s)) for s in divisors(n)), F(0)),
                             F(n, phi(n)))
            recovered = sum((F(mobius(s)**2*mobius(n//s)**2, phi(s))
                             for s in divisors(n) if gcd(s, n//s) == 1), F(0))/n
            self.assertEqual(recovered, F(mobius(n)**2, phi(n)))

    def test_squarefree_unit_ie_retains_every_divisor(self):
        for n, D0 in product(range(1, 200), (1, 6, 30, 77)):
            expanded = sum(mobius(u)*mobius(v)
                           for u in divisors(n) if n % (u*u) == 0 and gcd(u, D0) == 1
                           for v in divisors(D0) if (n//(u*u)) % v == 0)
            expected = mobius(n)**2 if gcd(n, D0) == 1 else 0
            self.assertEqual(expanded, expected)

    def test_square_unit_overlap_c4_D2_negative_regression(self):
        c, D0 = 4, 2
        wrong = sum(mobius(u)*mobius(v)
                    for u in divisors(c) if c % (u*u) == 0
                    for v in divisors(D0) if c % (u*u*v) == 0)
        repaired = sum(mobius(u)*mobius(v)
                       for u in divisors(c) if c % (u*u) == 0 and gcd(u, D0) == 1
                       for v in divisors(D0) if c % (u*u*v) == 0)
        self.assertEqual(wrong, -1)
        self.assertEqual(repaired, 0)
        self.assertNotEqual(wrong, repaired)

    def test_divisor_costs_with_improved_sqrt_fl(self):
        # Powers of f,l,j from the four raw mean terms in RP14.
        raw = ((1, 1, 2), (1, F(1, 2), F(3, 2)),
               (F(1, 2), 1, F(3, 2)), (F(1, 2), F(1, 2), 1))
        actual = tuple((a+F(1, 2), b+F(1, 2), c) for a, b, c in raw)
        self.assertEqual(actual, ((F(3, 2), F(3, 2), 2), (F(3, 2), 1, F(3, 2)),
                                  (1, F(3, 2), F(3, 2)), (1, 1, 1)))
        self.assertTrue(all(min(row) >= 1 for row in actual))

    def test_nonzero_frequency_ring_no_extra_one(self):
        for scale, d in product((F(1, 8), F(1, 2), F(1), F(7, 3), F(9)), range(1, 28)):
            count = sum(scale <= d*k < 2*scale for k in range(1, 60))
            self.assertLessEqual(count, 2*scale/d)
            if 2*scale <= d:
                self.assertEqual(count, 0)

    def test_zero_frequency_has_separate_small_bound(self):
        eta, J = F(6, 5), 12
        # RP7: 1-J + (R+Q+M+K-E)/2 in exponent notation.
        direct = 1-J+(3+(3-eta)+F(1, 2)+F(1, 2)-eta)/2
        self.assertEqual(direct, F(9, 2)-eta-J)
        self.assertLess(direct, 0)
        self.assertEqual(ram(6, 0), phi(6))  # It is present, not zero.


if __name__ == '__main__':
    unittest.main()
