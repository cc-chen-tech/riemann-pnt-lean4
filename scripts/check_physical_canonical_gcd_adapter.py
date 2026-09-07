#!/usr/bin/env python3
"""Finite guards for the physical canonical gcd adapter, not a gate proof."""

from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, isqrt
import unittest

from check_physical_large_gcd_type_columns import (
    mobius, phi, product_terms, raw_column, root_normal_form, units,
)
from check_physical_squarefree_type_descent import divisors
from check_physical_product_label_l2 import label_kernel, label_products


def canonical(s, h, delta):
    e = gcd(s, gcd(h, delta))
    a, b = gcd(s, h)//e, gcd(s, delta)//e
    return a, b, e, s//(a*b*e), h//(a*e), delta//(b*e)


class CanonicalGcdChecks(unittest.TestCase):
    def test_shared_prime_does_not_count_twice(self):
        # s=2*3*5*7, h=2*5*11, delta=3*5*13.
        self.assertEqual(canonical(210, 110, 195), (2, 3, 5, 7, 11, 13))

    def test_signed_labels_and_conductor_one(self):
        self.assertEqual(canonical(30, -110, 195), (2, 3, 5, 1, -11, 13))

    def test_forward_map_retains_all_canonical_masks(self):
        labels = tuple(range(-9, 0))+tuple(range(1, 10))
        for s in range(1, 65):
            if not mobius(s):
                continue
            for h, delta in product(labels, repeat=2):
                a, b, e, q, u, v = canonical(s, h, delta)
                self.assertTrue(all(gcd(x, y) == 1 for x, y in combinations((a, b, e, q), 2)))
                self.assertEqual((a*b*e*q, a*e*u, b*e*v), (s, h, delta))
                self.assertEqual((gcd(a, v), gcd(b, u), gcd(q, u*v)), (1, 1, 1))
                self.assertEqual(gcd(s, h*delta), a*b*e)
                self.assertEqual(gcd(s, gcd(h, delta)), e)
                self.assertEqual(mobius(s), mobius(a)*mobius(b)*mobius(e)*mobius(q))

    def test_reverse_map_is_unique_and_onto_finite_original_domain(self):
        for s in range(1, 43):
            if not mobius(s):
                continue
            original = {(h, delta) for h in range(-10, 11) if h
                        for delta in range(-10, 11) if delta}
            recovered = []
            for a in divisors(s):
                for b in divisors(s//a):
                    for e in divisors(s//(a*b)):
                        q = s//(a*b*e)
                        for u in range(-10//(a*e)-1, 10//(a*e)+2):
                            for v in range(-10//(b*e)-1, 10//(b*e)+2):
                                if not (0 < abs(a*e*u) <= 10 and 0 < abs(b*e*v) <= 10):
                                    continue
                                if gcd(a, v) > 1 or gcd(b, u) > 1 or gcd(q, u*v) > 1:
                                    continue
                                row = (a*e*u, b*e*v)
                                self.assertEqual(canonical(s, *row), (a, b, e, q, u, v))
                                recovered.append(row)
            self.assertEqual(set(recovered), original)
            self.assertEqual(len(recovered), len(original))

    def test_dropping_cross_masks_mislabels_the_common_gcd(self):
        self.assertEqual(canonical(30, 10, 30), (1, 3, 10, 1, 1, 1))
        self.assertNotEqual(canonical(30, 10, 30), (2, 3, 5, 1, 1, 2))
        self.assertNotEqual(canonical(30, 30, 15), (2, 3, 5, 1, 3, 1))

    def test_prime_assignment_requires_squarefree_s(self):
        self.assertEqual(gcd(4, 2*2), 4)
        a, b, e, q, u, v = canonical(4, 2, 2)
        self.assertNotEqual(gcd(e, q), 1)
        self.assertNotEqual(a*b*e, gcd(4, 4))

    def test_original_phase_not_real_ratio_or_extra_inverse_e(self):
        cases = 0
        for s in range(2, 45):
            if not mobius(s):
                continue
            for n in range(1, 12):
                if gcd(n, s) > 1:
                    continue
                for h, delta in product((-11, -5, -1, 2, 7), repeat=2):
                    a, b, e, q, u, v = canonical(s, h, delta)
                    original = F(-h*delta*pow(n, -1, s), s) % 1
                    reduced = F(-e*u*v*pow(n, -1, q), q) % 1
                    self.assertEqual(original, reduced)
                    cases += 1
        self.assertGreater(cases, 3000)
        self.assertNotEqual(F(-5*pow(11, -1, 7), 7) % 1,
                            F(-pow(5, -1, 7)*pow(11, -1, 7), 7) % 1)

    def test_full_mobius_sign_is_not_unsigned_overlap(self):
        a, b, e, q, n = 2, 3, 5, 7, 11
        full = mobius(n)*mobius(a*b*e*q)
        self.assertEqual(full, -1)
        wrong = mobius(n)*mobius(a)*mobius(b)*mobius(e)**2*mobius(q)
        self.assertEqual(wrong, 1)

    def test_mollifier_q0_coprimality_is_not_optional(self):
        q0, a, b, e, q = 11, 2, 3, 5, 7
        for n in range(1, 75):
            original = mobius(q0*n)*mobius(q0*a*b*e*q)
            restored = (mobius(n)*mobius(a)*mobius(b)*mobius(e)*mobius(q)
                        if gcd(n, q0*a*b*e*q) == 1 else 0)
            if gcd(n, a*b*e*q) == 1:
                self.assertEqual(original, restored)
        self.assertEqual(mobius(q0*q0), 0)

    def test_whole_type_row_plus_principal_retains_cross_masks(self):
        fixtures = [(2, 3, 5, 11, q) for q in (1, 7, 13, 17)]
        fixtures += [(7, 11, 13, 17, q) for q in (6, 30)]
        for a, b, e, q0, q in fixtures:
            bu = {u: F((-1)**abs(u), abs(u)+1) for u in (-3, -2, -1, 1, 2, 3) if gcd(u, b) == 1}
            cv = {v: F(1, abs(v)+1) for v in (-3, -2, -1, 1, 2, 3) if gcd(v, a) == 1}
            coeff = {n: F(mobius(n), n+1) for n in range(1, 15) if gcd(n, q0*a*b*e) == 1}
            labels = label_products(bu, cv, 1, q)
            beta = F(mobius(a*b*e*q), 2)
            actual = [(-e*m*pow(n, -1, q), beta*x*y) for n, x in coeff.items()
                      if gcd(n, q) == 1 for m, y in labels]
            W = sum((y for m, y in labels), F(0))
            whole = [(0, beta*x*W*F(mobius(q), phi(q)))
                     for n, x in coeff.items() if gcd(n, q) == 1]
            for d in divisors(q):
                ell = q//d
                for t in units(ell):
                    kernel = [(d*z, y) for z, y in label_kernel(ell, t, e, d, labels)]
                    whole += product_terms(raw_column(q, d*t, coeff), kernel, beta*F(mobius(d), q))
            self.assertEqual(root_normal_form(q, actual), root_normal_form(q, whole))

    def test_scaled_weight_is_identical_in_all_four_coordinates(self):
        a, b, e, Q, R, S, H, L = map(F, (2, 3, 5, 17, 101, 511, 37, 41))
        U, V = H/(a*e), L/(b*e)
        for d in (1, 2, 7):
            n, ell, u, v = map(F, (71, 3, -2, 4))
            self.assertEqual((n/R, a*b*e*d*ell/S, b*e*v/L, a*e*u/H),
                             (n/R, (a*b*e*Q/S)*(ell/(Q/d)), v/V, u/U))

    def test_small_label_endpoints_are_empty_or_at_least_half(self):
        for H, ae in product(range(1, 16), repeat=2):
            U = F(H, ae)
            actual = [u for u in range(-30, 31) if u and abs(ae*u) <= 2*H]
            if actual:
                self.assertGreaterEqual(U, F(1, 2))
            else:
                self.assertLess(U, F(1, 2))

    def test_all_abe_counting_cost_not_just_one_row(self):
        for A, B, E in product((1, 2, 4, 8), repeat=3):
            # Half-open positive dyadic shells [A,2A) include the endpoint 1.
            harmonic = sum((F(1, a*b*e*e) for a in range(A, 2*A)
                            for b in range(B, 2*B) for e in range(E, 2*E)), F(0))
            self.assertLessEqual(harmonic, F(1, E))
            self.assertEqual(A*B*E*F(1, A*B*E*E), F(1, E))
            # Sum 1/(e sqrt(ab)) <= sqrt(AB); square the counting upper bound.
            self.assertEqual(F((A*B*E)**2, E*E*A*B), A*B)

    def test_simplified_bound_has_no_missing_D_or_S(self):
        T, R, S, D, E = map(F, (64, 83, 510, 30, 5))
        Q, HL = S/D, R*S/T
        first_squared = (T/(R*S))**2*HL*(D/E)*Q*R*(R+Q*Q)
        self.assertEqual(first_squared, T*(R+Q*Q)/E)
        self.assertEqual((T/(R*S))*HL/E, 1/E)

    def test_new_nontrivial_allocation_cost_and_remaining_region(self):
        eta, delta = F(9, 4), F(13, 5)
        Qexp = 3-delta
        first = (1+max(F(3), 2*Qexp)-eta)/2
        second = max(F(3), F(3, 2)+Qexp)-eta
        raw = 6-delta-eta
        self.assertEqual((first, second, raw), (F(7, 8), F(3, 4), F(23, 20)))
        self.assertEqual(raw-max(first, second), F(11, 40))
        self.assertGreater(3-F(19, 10), 1)

    def test_bertrand_family_has_growing_a_and_b_and_small_labels(self):
        A, B, E, Q = map(F, (7, 7, 90, 16))
        S, T = A+B+E+Q, (A+B+E+Q)/3
        H = S-T/2
        self.assertEqual((T, E/T, (A+B+E)/T), (40, F(9, 4), F(13, 5)))
        self.assertEqual((H-A-E, H-B-E), (3, 3))
        self.assertLess(3, min(A, B, Q))

    def test_explicit_nonempty_original_box_beyond_FP3(self):
        # All values exact, with T=512 and N=T^3; no assumed nonzero W integral.
        a, b, e, q, n = 2, 3, 65537, 31, 12190157
        # primality is not needed for n: check its actual squarefreeness and units.
        self.assertTrue(all(mobius(m) for m in (a, b, e, q, n)))
        s, T = a*b*e*q, 512
        R = S = s
        N = T**3
        H = L = F(s, isqrt(T)+1)
        # Choose labels separately, retaining (b,u)=(a,v)=1.
        u, v = 5, 3
        h, delta = a*e*u, b*e*v
        self.assertEqual(canonical(s, h, delta), (a, b, e, q, u, v))
        self.assertEqual(gcd(n, s), 1)
        self.assertTrue(R <= n <= 2*R and 2*S <= N//2)
        self.assertTrue(H <= h <= 2*H and L <= delta <= 2*L)
        self.assertLessEqual(H*L, F(R*S, T))
        self.assertLessEqual(max(n, s), N//4)
        # Kz=Mz=sqrt(T); compare squared rational endpoints, without floats.
        x = F(17)
        y = (x*n+delta)/s
        self.assertTrue(F(T, 4) <= x*x <= 4*T)
        self.assertTrue(F(T, 4) <= y*y <= 4*T)
        E, Q = 65536, 16
        self.assertTrue(E <= e < 2*E and Q <= q < 2*Q)
        self.assertGreaterEqual(E, F(R+Q*Q, T))


if __name__ == "__main__":
    unittest.main()
