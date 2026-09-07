#!/usr/bin/env python3
"""Exact inactive-product-band guards; not an analytic large-sieve proof."""
from fractions import Fraction as F
from math import gcd
from itertools import product
from collections import defaultdict
from functools import lru_cache
import unittest

from check_physical_type_i_triple_completion import triple_spectrum
from check_physical_type_ii_common_frequency_band import (
    band_weight, gamma_column, kernel_poly, physical_exponents)
from check_physical_centered_conductor_split import roots_equal, prime_factors
from check_physical_squarefree_type_descent import divisors
from check_physical_large_gcd_type_columns import mobius, phi


@lru_cache(None)
def inactive_masks(r):
    terms = [(F(1), 1, 1, 1)]
    for p in prime_factors(r):
        next_terms = []
        a = F(p-1, p)
        for bits in range(7):
            size = bin(bits).count('1')
            scalar = -(-1)**size*a**(3-size)/(p-1)
            for coefficient, rn, ru, rv in terms:
                next_terms.append((coefficient*scalar,
                    rn*(p if bits & 1 else 1), ru*(p if bits & 2 else 1),
                    rv*(p if bits & 4 else 1)))
        terms = next_terms
    return tuple(terms)


def inactive_kernel(r, n, u, v):
    return sum(coefficient for coefficient, rn, ru, rv in inactive_masks(r)
               if gcd(n, rn) == gcd(u, ru) == gcd(v, rv) == 1)


def product_band(q, k, rho, sigma, cutoff):
    return sum(band_weight(r, cutoff) for r in divisors(gcd(q, k*rho*sigma)))


def projected_product_poly(q, r, alpha, n, u, v):
    ell = q//r
    if ell == 1:
        return {}
    factor = inactive_kernel(r, n, u, v)
    return {r*phase: factor*coefficient for phase, coefficient in
            kernel_poly(ell, alpha*pow(r, -1, ell) % ell, n, u, v).items()}


class ProductBandTests(unittest.TestCase):
    def test_local_seven_terms_are_not_just_the_common_zero_mean(self):
        self.assertEqual(inactive_kernel(3, 1, 1, 1), F(-13, 27))

    def test_absolute_mask_coefficients_pay_all_seven_terms(self):
        self.assertEqual(sum(abs(a) for a, *_ in inactive_masks(2)), F(19, 8))

    def test_product_band_strictly_extends_common_band(self):
        self.assertEqual(product_band(15, 1, 3, 1, 3), 1)
        self.assertEqual(gcd(15, gcd(1, gcd(3, 1))), 1)
        self.assertEqual(triple_spectrum(15, 1, 1, 3, 1), F(25, 4))

    def test_crt_inverse_phase_and_no_extra_r_cubed(self):
        self.assertEqual(projected_product_poly(15, 3, 1, 2, 1, 1),
                         {12: F(-13, 27), 0: F(-13, 108)})

    def test_seven_masks_equal_local_projection_polynomial(self):
        for r in (1, 2, 3, 6, 10, 15, 30):
            for n, u, v in product(range(4), repeat=3):
                direct = F(1)
                for p in prime_factors(r):
                    a = F(p-1, p)
                    x, y, z = (int(t % p != 0) for t in (n, u, v))
                    direct *= -(x*y*z-(x-a)*(y-a)*(z-a))/(p-1)
                self.assertEqual(inactive_kernel(r, n, u, v), direct)

    def test_mask_budget_and_allowed_overlaps(self):
        for r in (1, 2, 3, 6, 10, 15, 30):
            terms = inactive_masks(r)
            self.assertEqual(len(terms), 7**len(prime_factors(r)))
            self.assertLessEqual(sum(abs(a) for a, *_ in terms),
                                 F(7**len(prime_factors(r)), phi(r)))
            self.assertTrue(all(gcd(rn, gcd(ru, rv)) == 1 for _, rn, ru, rv in terms))
        self.assertTrue(any(gcd(ru, rv) > 1 for _, _, ru, rv in inactive_masks(6)))

    def test_full_local_average_recovers_common_zero_projection(self):
        for r in (1, 2, 3, 6, 10):
            average = sum(inactive_kernel(r, *point)
                          for point in product(range(r), repeat=3))/r**3
            self.assertEqual(average, F(mobius(r)*phi(r)**2, r**3))

    def test_nonunit_n_is_not_remasked_after_projection(self):
        self.assertEqual(inactive_kernel(3, 0, 1, 1), F(-1, 27))
        value = projected_product_poly(15, 3, 1, 3, 1, 1)
        self.assertFalse(roots_equal([(F(k, 15), a) for k, a in value.items()], []))
        self.assertEqual(kernel_poly(15, 1, 3, 1, 1), {})

    def test_exact_finite_inverse_not_product_of_local_centers(self):
        spectrum = lru_cache(None)(triple_spectrum)
        for q in (3, 6, 10, 15):
            for r in divisors(q):
                for n, u, v in ((0, 1, 1), (1, 1, 1), (2, 3, 1), (3, 2, 1)):
                    direct = defaultdict(F)
                    for k, rho, sigma in product(range(q), repeat=3):
                        if k*rho*sigma % r == 0:
                            direct[-(k*n+rho*u+sigma*v) % q] += (
                                spectrum(q, 1, k, rho, sigma)/q**3)
                    crt = projected_product_poly(q, r, 1, n, u, v)
                    self.assertTrue(roots_equal([(F(k, q), a) for k, a in direct.items()],
                                               [(F(k, q), a) for k, a in crt.items()]))

    def test_band_uses_signed_divisor_weights_and_real_cutoffs(self):
        for q, cutoff in product((3, 6, 10, 15, 30), (F(1), F(3, 2), F(3), F(17, 2))):
            for k, rho, sigma in product(range(4), repeat=3):
                self.assertEqual(product_band(q, k, rho, sigma, cutoff),
                                 int(gcd(q, k*rho*sigma) >= cutoff))
        self.assertEqual(band_weight(6, 2), -1)

    def test_new_band_is_difference_of_nested_projectors(self):
        for q, cutoff in product((6, 15, 30), (2, 3, 5)):
            for k, rho, sigma in product(range(5), repeat=3):
                common = gcd(q, gcd(k, gcd(rho, sigma)))
                prod = gcd(q, k*rho*sigma)
                new = product_band(q, k, rho, sigma, cutoff)-int(common >= cutoff)
                self.assertEqual(new, int(common < cutoff <= prod))

    def test_prime_high_band_and_level_one_are_zero(self):
        for q in (2, 3, 5, 7):
            for k, rho, sigma in product(range(q), repeat=3):
                if product_band(q, k, rho, sigma, 2):
                    self.assertEqual(triple_spectrum(q, 1, k, rho, sigma), 0)
            self.assertEqual(projected_product_poly(q, q, 1, 1, 1, 1), {})

    def test_assigned_n_mask_not_full_r_mask_in_common_column(self):
        self.assertEqual(gamma_column(12, 3, 1, 1), 1)
        self.assertNotEqual(inactive_kernel(3, 12, 1, 1), 0)
        self.assertEqual(gcd(12, 3), 3)
        for e, r, n in product((2, 3, 5), (2, 3, 6), range(1, 31)):
            if gcd(e, r) > 1:
                continue
            for _, rn, _, _ in inactive_masks(r):
                lhs = mobius(e)*int(gcd(e, n) == gcd(n, rn) == 1)
                rhs = sum(mobius(f)**2*mobius(e//f)
                          for f in divisors(gcd(e, n))
                          if gcd(e//f, f) == gcd(n//f, rn) == 1)
                self.assertEqual(lhs, rhs)

    def test_false_t_f_condition_changes_required_ie_cancellation(self):
        e, n = 2, 4
        exact = sum(mobius(f)**2*mobius(e//f) for f in divisors(gcd(e, n)))
        wrong = sum(mobius(f)**2*mobius(e//f) for f in divisors(gcd(e, n))
                    if gcd(n//f, f) == 1)
        self.assertEqual((exact, wrong), (0, -1))

    def test_full_nonseparable_packet_B_Gamma_and_assigned_ie(self):
        for e, r, ell in ((2, 3, 5), (3, 2, 5), (5, 6, 7), (7, 10, 3)):
            q = r*ell
            out = [defaultdict(F) for _ in range(3)]
            for n in range(1, 39):
                for u, v in product((-2, -1, 1, 2), repeat=2):
                    weight = F(2*n+u*v+3*u-2*v, 101)
                    raw = F(0)
                    for b in divisors(n):
                        for c in divisors(n//b):
                            B = b*c
                            if b > 1 and c > 1 and gcd(B, e*q) == gcd(n//B, e) == 1:
                                raw += mobius(b)*mobius(c)*inactive_kernel(r, n//B, u, v)
                    gam = gamma_column(n, r, 1, 1)
                    joined = gam*int(gcd(n, e) == 1)*inactive_kernel(r, n, u, v)
                    ie = sum(mobius(f)**2*mobius(e//f)*gam*coefficient
                             for f in divisors(gcd(e, n))
                             for coefficient, rn, ru, rv in inactive_masks(r)
                             if gcd(e//f, f) == gcd(n//f, rn) == gcd(u, ru) == gcd(v, rv) == 1)
                    for i, coefficient in enumerate((mobius(e)*raw, mobius(e)*joined, ie)):
                        for phase, a in kernel_poly(ell, e*pow(r, -1, ell) % ell, n, u, v).items():
                            out[i][phase] += mobius(q)*coefficient*weight*a
            for i in (1, 2):
                self.assertTrue(roots_equal([(F(k, ell), a) for k, a in out[0].items()],
                                           [(F(k, ell), a) for k, a in out[i].items()]))

    def test_enlarged_label_ie_keeps_overlap_and_primitive_units(self):
        for r, c, ell in ((6, 5, 7), (10, 3, 7), (3, 2, 5)):
            for _, _, ru, rv in inactive_masks(r):
                for u, v in product(range(1, 8), repeat=2):
                    exact = int(gcd(u, c*ru) == gcd(v, c*rv) == 1)
                    expanded = sum(mobius(j)*mobius(k)
                                   for j in divisors(c*ru) for k in divisors(c*rv)
                                   if u % j == v % k == 0)
                    self.assertEqual(exact, expanded)
                self.assertTrue(all(gcd(j*k, ell) == 1
                                    for j in divisors(c*ru) for k in divisors(c*rv)))

    def test_double_poisson_cost_has_no_extra_r_denominator(self):
        vals = (F(1, 2), F(1), F(3))
        for A, B, lam, U, V in product(vals, repeat=5):
            for j, k in ((1, 1), (2, 3), (6, 6)):
                K = A*lam**2*j*k/(U*V)
                lhs = (U*V)**2/(j*k)**2/lam**3*B*K*(B+lam**2)*(K+lam**2)
                rhs = A*B*lam*(B+lam**2)*(A+U*V/(j*k))
                self.assertEqual(lhs, rhs)

    def test_extra_divisor_count_is_not_extra_modulus_count(self):
        for r, c in ((6, 5), (10, 3), (30, 7)):
            for _, _, ru, rv in inactive_masks(r):
                self.assertLessEqual(len(divisors(c*ru))*len(divisors(c*rv)),
                                     len(divisors(c))**2*len(divisors(r))**2)

    def test_quotient_dilation_preserves_product_gcd(self):
        for q, d, k, rho, sigma in product((6, 15, 30), (1, 7, 11), range(4), range(4), range(4)):
            if gcd(d, q) == 1:
                self.assertEqual(gcd(q, d*k*rho*sigma), gcd(q, k*rho*sigma))

    def test_new_physical_support_not_just_a_fourier_far_tail(self):
        e, r, ell, b, c, m = 101, 5, 103, 29, 31, 59
        q, B = r*ell, b*c
        S = R = e*q
        T = (8*S)**(1/3)
        H = L = S/T**.5
        n = B*m
        self.assertTrue(R/2 <= n <= 2*R)
        self.assertEqual(gcd(n, e*q), 1)
        self.assertEqual(gcd(q, gcd(1, gcd(r, 1))), 1)
        self.assertEqual(gcd(q, r), r)
        self.assertTrue(1 <= q*B/R and r <= q*e/H and 1 <= q*e/L)
        self.assertNotEqual(triple_spectrum(q, e*pow(B, -1, q) % q, 1, r, 1), 0)
        self.assertEqual(max(physical_exponents(F(6, 5), F(1, 10))), F(19, 20))
        self.assertEqual(max(physical_exponents(F(6, 5), F(1, 15))), 1)


if __name__ == '__main__':
    unittest.main()
