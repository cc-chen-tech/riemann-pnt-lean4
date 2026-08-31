#!/usr/bin/env python3
"""Exact finite guards for a specified physical large-gcd family.

These tests check identities, masks, normalization and rational exponents.
They do NOT prove the additive large sieve, AFE smoothness, arbitrary-scale
estimates, coverage outside the declared family, or any zero-free theorem.
The analytic argument and physical hypotheses are in the companion note.
"""

from collections import defaultdict
from fractions import Fraction as F
from math import gcd
import unittest

from check_pre_cauchy_common_determinant import mobius, root_normal_form
from check_common_frequency_parseval_conductor_average import square_terms


def units(q):
    return [n for n in range(q) if gcd(n, q) == 1]


def phi(q):
    return len(units(q))


def primes(lo, hi):
    return [p for p in range(lo + 1, hi + 1)
            if p >= 2 and all(p % d for d in range(2, int(p**0.5) + 1))]


def kernel(q, k, A):
    """Centered Kloosterman Fourier kernel; A must be a unit."""
    assert gcd(A, q) == 1 and mobius(q) != 0
    return [(k*x - A*pow(x, -1, q), F(1)) for x in units(q)] + [
        (k*x, -F(mobius(q), phi(q))) for x in units(q)]


def raw_column(q, k, coeff):
    return [(-k*n, a) for n, a in coeff.items() if gcd(n, q) == 1]


def product_terms(left, right, scale=F(1)):
    return [(x+y, scale*a*b) for x, a in left for y, b in right]


def completed_part(g, p, A, coeff, crowded):
    q = g*p
    result = []
    for k in range(q):
        if (k % p == 0) == crowded:
            result += product_terms(raw_column(q, k, coeff), kernel(q, k, A), F(1, q))
    return result


def lower_g_part(g, p, A, coeff):
    # Embedded as roots of order gp. The p inverse cannot be discarded.
    return [(p*(-A*pow(p, -1, g)*pow(n, -1, g)), -a/p)
            for n, a in coeff.items() if gcd(n, g*p) == 1] + [
        (0, a*F(mobius(g), p*phi(g)))
        for n, a in coeff.items() if gcd(n, g*p) == 1]


def physical_exponents(r, s, h, ell, eta, gamma, pi, q0=F(0)):
    prefactor = 1-q0-r-s
    return {
        "counting": prefactor+r+h+ell+gamma+pi-eta,
        "noncrowded": prefactor+h+ell+gamma-eta+(pi+r+max(r, gamma+2*pi))/2,
        "crowded": prefactor+r+h+ell+gamma-eta,
        "principal": prefactor+r+h+ell-eta,
    }


class PhysicalLargeGcdChecks(unittest.TestCase):
    def roots_equal(self, q, left, right):
        self.assertEqual(root_normal_form(q, left), root_normal_form(q, right))

    @staticmethod
    def coeff(length=13):
        return {n: F((-1)**n*(n % 5+1), n+1) for n in range(1, length+1)}

    def test_unit_mask_split_exact(self):
        a = self.coeff()
        for g, p in ((1, 5), (3, 5), (5, 3), (6, 5)):
            for k in range(g*p):
                direct = [(-k*n, c) for n, c in a.items() if n % p]
                full = [(-k*n, c) for n, c in a.items()]
                correction = [(-k*n, -c) for n, c in a.items() if n % p == 0]
                self.roots_equal(g*p, direct, full+correction)

    def test_dropping_p_mask_changes_column(self):
        self.assertNotEqual(root_normal_form(15, []), root_normal_form(15, [(-5, F(1))]))

    def test_mask_energy_exact(self):
        a = self.coeff(25)
        for g, p in ((1, 3), (2, 3), (3, 5), (5, 7), (6, 5)):
            ap = {m: a[p*m] for m in range(1, 25//p+1)}
            left = []
            for k in range(g*p):
                if k % p:
                    left += square_terms(g, [(-k*m, c) for m, c in ap.items()])
            rows = defaultdict(F)
            for m, c in ap.items():
                rows[m % g] += c
            right = (p-1)*g*sum((c*c for c in rows.values()), F(0))
            self.roots_equal(g, left, [(0, right)])

    def test_mask_endpoint_bound(self):
        for X in range(1, 18):
            for g, p in ((1, 3), (3, 5), (5, 7)):
                counts = [sum(m % g == r for m in range(1, 2*X//p+1)) for r in range(g)]
                self.assertLessEqual(max(counts), F(2*X, p*g)+1)

    def test_subsequence_energy_is_divisor_count(self):
        a = self.coeff(50)
        ps = [p for p in primes(3, 6) if gcd(p, 3) == 1]
        left = sum((c*c for p in ps for n, c in a.items() if n % p == 0), F(0))
        right = sum((c*c*sum(n % p == 0 for p in ps) for n, c in a.items()), F(0))
        self.assertEqual(left, right)

    def test_divisor_count_uses_only_allowed_primes(self):
        g, n = 7, 77
        full = primes(6, 12)
        allowed = [p for p in full if gcd(p, g) == 1]
        self.assertEqual(sum(n % p == 0 for p in allowed), 1)
        self.assertEqual(sum(n % p == 0 for p in full), 2)

    def test_strong_common_g_circle_spacing(self):
        P = 6
        for g in (1, 2, 3, 5, 6, 15):
            xs = [F(k, g*p) for p in (7, 11) if gcd(p, g) == 1
                  for k in range(g*p) if k % p]
            self.assertEqual(len(xs), len(set(xs)))
            xs.sort()
            gaps = [y-x for x, y in zip(xs, xs[1:])] + [1+xs[0]-xs[-1]]
            self.assertGreaterEqual(min(gaps), F(1, 4*g*P*P))

    def test_low_denominator_keeps_second_p(self):
        g, p, j = 3, 5, 1
        self.assertNotEqual(F(p*j, g) % 1, F(j, g) % 1)

    def test_type_descent_including_zero(self):
        for g in (1, 2, 3, 5, 6, 15):
            p = 7
            for j in range(g):
                d = gcd(j, g)
                self.assertEqual(gcd(p*j, p*g), p*d)
                self.assertEqual(p*g//gcd(p*j, p*g), g//d)

    def test_kernel_parseval_exact(self):
        for q in (2, 3, 5, 6, 10, 15, 21):
            for A in (1, 2, 5):
                if gcd(A, q) != 1:
                    continue
                left = [term for k in range(q) for term in square_terms(q, kernel(q, k, A))]
                self.roots_equal(q, left, [(0, q*(F(phi(q))-F(1, phi(q))))])

    def test_kernel_zero_mode_exact(self):
        for q in (2, 3, 5, 6, 15):
            self.roots_equal(q, kernel(q, 0, 1), [])

    def test_rank_one_correction_cannot_be_deleted(self):
        for q in (3, 5, 15):
            uncentered = [(-pow(x, -1, q), F(1)) for x in units(q)]
            self.roots_equal(q, uncentered, [(0, mobius(q))])
            self.assertNotEqual(root_normal_form(q, uncentered), root_normal_form(q, []))

    def test_crowded_low_g_full_inverse_exact(self):
        a = self.coeff(9)
        for g, p in ((1, 5), (2, 3), (3, 5), (5, 3), (6, 5)):
            for A in (1, 2):
                if gcd(A, g*p) == 1:
                    self.roots_equal(g*p, completed_part(g, p, A, a, True), lower_g_part(g, p, A, a))

    def test_complete_three_parts_reconstruct_original(self):
        a = self.coeff(9)
        for g, p in ((1, 5), (3, 5), (5, 3), (6, 5)):
            q, A = g*p, 1
            original = [(-A*pow(n, -1, q), c) for n, c in a.items() if gcd(n, q) == 1]
            principal = [(0, c*F(mobius(q), phi(q))) for n, c in a.items() if gcd(n, q) == 1]
            full = principal + lower_g_part(g, p, A, a) + completed_part(g, p, A, a, False)
            self.roots_equal(q, original, full)

    def test_g_one_crowded_is_empty(self):
        self.roots_equal(5, completed_part(1, 5, 1, self.coeff(), True), [])

    def test_p_inverse_is_not_optional(self):
        right = lower_g_part(3, 5, 1, {1: F(1)})
        wrong = [(-5, F(-1, 5)), (0, F(-1, 10))]
        self.assertNotEqual(root_normal_form(15, right), root_normal_form(15, wrong))

    def test_overlap_positive_term_is_not_real_mu_layer(self):
        self.assertEqual(-1-1+1, mobius(5))
        self.assertNotEqual(mobius(5), mobius(5)**2)

    def test_largest_prime_label_is_unique(self):
        for Q in (15, 21, 33, 35, 39, 55):
            admitted = [(g, p) for p in primes(1, Q) if Q % p == 0
                        for g in (Q//p,) if p > g]
            self.assertLessEqual(len(admitted), 1)
        self.assertEqual([(15//p, p) for p in (3, 5)], [(5, 3), (3, 5)])

    def test_signed_nonzero_label_count_needs_no_plus_one(self):
        for H in range(1, 12):
            for e in range(1, 30):
                count = 2*(2*H//e)
                self.assertLessEqual(count, F(4*H, e))
                if e > 2*H:
                    self.assertEqual(count, 0)

    def test_overlap_inverse_square_sum(self):
        for E in range(1, 30):
            self.assertLessEqual(sum((F(1, e*e) for e in range(E+1, 2*E+1)), F(0)), F(1, E))

    def test_prime_cofactor_weights_pay_count(self):
        for P in range(2, 30):
            self.assertLessEqual(sum((F(1, p) for p in primes(P, 2*P)), F(0)), 1)
            self.assertLessEqual(sum((F(1, p-1) for p in primes(P, 2*P)), F(0)), 1)

    def test_totient_factorization_not_squared(self):
        for g, p in ((1, 5), (3, 5), (6, 5), (15, 7)):
            self.assertEqual(phi(g*p), phi(g)*(p-1))

    def test_physical_outer_factor_is_used_once(self):
        T, q0, R, S, E, G = map(F, (64, 3, 32768, 16384, 2000, 2))
        HL = R*S/T
        core = R*HL*G/E
        self.assertEqual(2*T/(q0*R*S)*core, 2*R*G/(q0*E))

    def test_exact_example_exponents(self):
        result = physical_exponents(F(3), F(3), F(5, 2), F(5, 2), F(49, 20), F(1, 5), F(7, 20))
        self.assertEqual(result, {"counting": F(11, 10), "noncrowded": F(37, 40),
                                  "crowded": F(3, 4), "principal": F(11, 20)})
        self.assertEqual(result["counting"]-result["noncrowded"], F(7, 40))
        self.assertEqual(1-result["noncrowded"], F(3, 40))

    def test_an_uncovered_scale_is_not_promoted(self):
        result = physical_exponents(F(3), F(3), F(5, 2), F(5, 2), F(11, 5), F(1, 5), F(3, 5))
        self.assertGreater(result["noncrowded"], 1)

    def test_real_integer_support_witness(self):
        T, R, H = 64, 32768, 4096
        e, g, p, n, u, v = 2003, 3, 5, 30011, 4, 4
        s, h, delta = e*g*p, e*u, e*v
        self.assertTrue(all(mobius(z) != 0 for z in (e, g, p, n)))
        self.assertEqual(gcd(n, e*g*p), 1)
        self.assertEqual(gcd(e, g*p), 1)
        self.assertEqual(gcd(u*v, g*p), 1)
        self.assertEqual(gcd(h*delta, s), e)
        self.assertTrue(R/2 <= n <= 2*R and R/2 <= s <= 2*R)
        self.assertTrue(H <= h <= 2*H and H <= delta <= 2*H)
        self.assertTrue(s <= T**3/2 and n <= T**3/2)
        self.assertTrue(4 <= F(8*n+delta, s) <= 16)
        self.assertGreaterEqual(1500*T, R*2)

    def test_bertrand_family_exponent_geometry(self):
        g, p, e = map(F, (4, 7, 49))
        t = (g+p+e)/3
        label = 3*t-t/2-e
        self.assertEqual(t, 20)
        self.assertEqual(label, 1)
        self.assertLess(label, g)
        self.assertLess(g, p)
        self.assertEqual(e-(3*t+g+p/2-t), F(3, 2))

    def test_joint_smooth_weight_is_not_assumed_rank_one(self):
        # Finite polynomial guard only, not an AFE smoothness certificate.
        # n+p needs two common-n atoms; its p dependence cannot be ignored.
        w = lambda n, p: n+p
        self.assertNotEqual(w(1, 3)*w(2, 5), w(1, 5)*w(2, 3))
        for n in (1, 2, 3):
            for p in (3, 5, 7):
                self.assertEqual(w(n, p), n*1+1*p)


if __name__ == "__main__":
    unittest.main()
