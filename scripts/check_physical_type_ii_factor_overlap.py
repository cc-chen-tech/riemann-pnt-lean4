#!/usr/bin/env python3
"""Finite factor-overlap guards; not an analytic gate or large-sieve proof."""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import gcd, isqrt, floor, ceil
import unittest

from check_physical_large_gcd_type_columns import mobius, phi
from check_physical_squarefree_type_descent import divisors
from check_physical_type_ii_common_frequency_band import kernel_poly
from check_physical_centered_conductor_split import roots_equal
from check_physical_type_i_triple_completion import triple_spectrum


@lru_cache(None)
def factor_pairs(n, lower, product_cutoff, overlap):
    return tuple((b, c) for b in divisors(n) for c in divisors(n//b)
                 if b > lower and c > lower and b*c > product_cutoff
                 and gcd(b, c) >= overlap)


@lru_cache(None)
def gamma(n, lower=1, product_cutoff=0, overlap=2):
    return sum(mobius(b)*mobius(c)
               for b, c in factor_pairs(n, lower, product_cutoff, overlap))


def has_square_witness(n, overlap):
    return any(mobius(g) and n % (g*g) == 0
               for g in range(max(1, ceil(overlap)), isqrt(n)+1))


def physical_exponents(eta, gamma_exponent):
    eta, gamma_exponent = F(eta), F(gamma_exponent)
    return tuple(v-gamma_exponent/2 for v in
                 ((eta-1)/2, 2-eta, 1-eta/2, F(7, 2)-2*eta))


class FactorOverlapTests(unittest.TestCase):
    def test_literal_nonsquarefree_expanded_term_is_not_zero(self):
        self.assertEqual(gamma(4), 1)
        self.assertEqual(mobius(4), 0)

    def test_overlap_does_not_mean_frequency_gcd(self):
        self.assertEqual(gcd(5, 1*1*1), 1)
        self.assertEqual(gamma(4), 1)
        self.assertNotEqual(triple_spectrum(5, 1, 1, 1, 1), 0)

    def test_signed_coefficient_not_unsigned_pair_count(self):
        self.assertEqual(gamma(12), -1)
        self.assertNotEqual(gamma(12), len(factor_pairs(12, 1, 0, 2)))

    def test_no_t_f_mask_after_full_inclusion_exclusion(self):
        correct = sum(mobius(f)**2*mobius(2//f)*gamma(4)
                      for f in divisors(2))
        wrong = sum(mobius(f)**2*mobius(2//f)*gamma(4)
                    for f in divisors(2) if gcd(4//f, f) == 1)
        self.assertEqual((correct, wrong), (0, -1))

    def test_square_period_retains_overlap_with_f(self):
        self.assertEqual(gamma(49, overlap=7), 1)
        self.assertEqual(7*7//gcd(7, 7), 7)
        self.assertEqual(7*7 % 49, 0)
        self.assertNotEqual(7 % 49, 0)

    def test_squarefree_f_hypothesis_is_essential(self):
        f, overlap, B = 17**2, 17, 20
        cardinal = sum(f*t % (overlap**2) == 0 for t in range(1, B+1))
        self.assertGreater(cardinal, F(4*B*len(divisors(f)), overlap))

    def test_empty_large_overlap_layer(self):
        for n in range(1, 101):
            self.assertEqual(gamma(n, overlap=isqrt(n)+1), 0)

    def test_all_pair_subsets_have_support_and_divisor_bound(self):
        for n, G, lower, cutoff in product(range(1, 301),
                (1, F(3, 2), 2, 3, 5), (0, 2), (0, 15)):
            value = gamma(n, lower, cutoff, G)
            tau3 = sum(len(divisors(n//b)) for b in divisors(n))
            self.assertLessEqual(abs(value), tau3)
            if value:
                self.assertTrue(has_square_witness(n, G))
            if G > 1 and mobius(n):
                self.assertEqual(value, 0)

    def test_full_e_n_ie_with_signed_common_coefficient(self):
        for e, n, G in product(range(1, 31), range(1, 81), (2, 3, 5)):
            if not mobius(e):
                continue
            left = mobius(e)*gamma(n, overlap=G)*int(gcd(e, n) == 1)
            right = sum(mobius(f)**2*mobius(e//f)*gamma(n, overlap=G)
                        for f in divisors(gcd(e, n)) if gcd(f, e//f) == 1)
            self.assertEqual(left, right)

    def test_totient_density_identity_with_shared_f(self):
        for f, g in product(range(1, 61), range(1, 61)):
            self.assertEqual(gcd(g, f), sum(phi(d) for d in divisors(gcd(g, f))))

    def test_uniform_sparse_count_including_subunit_B(self):
        for f, B, G in product(range(1, 41),
                (F(1, 2), F(1), F(3, 2), F(7, 2), F(11)), (1, 2, 3, 5, 11)):
            if not mobius(f):
                continue
            ts = range(1, floor(2*B)+1)
            actual = sum(has_square_witness(f*t, G) for t in ts)
            self.assertLessEqual(actual, 4*B*len(divisors(f))/G)
            for g in range(1, isqrt(floor(2*f*B))+1):
                if mobius(g):
                    period = g*g//gcd(g, f)
                    self.assertTrue(all((f*t % (g*g) == 0) == (t % period == 0)
                                        for t in ts))

    def test_actual_common_column_energy_finite_majorant(self):
        for f, B, G in product((1, 2, 3, 6, 7, 10, 15, 30),
                              (F(1, 2), F(3, 2), F(5), F(13)), (2, 3, 5, 11)):
            ts = range(max(1, ceil(B/2)), floor(2*B)+1)
            tau_max = max(sum(len(divisors(f*t//b)) for b in divisors(f*t))
                          for t in ts)
            energy = sum(gamma(f*t, overlap=G)**2 for t in ts)
            self.assertLessEqual(energy, tau_max**2*4*B*len(divisors(f))/G)

    def test_linear_low_high_partition_with_real_thresholds(self):
        for n, G in product(range(1, 201), (F(3, 2), F(7, 2), F(11, 2))):
            total = gamma(n, overlap=1)
            low = sum(mobius(b)*mobius(c) for b, c in factor_pairs(n, 1, 0, 1)
                      if gcd(b, c) < G)
            self.assertEqual(total, low+gamma(n, overlap=G))

    def test_full_signed_kernel_reassembly_with_complex_joint_weight(self):
        for q, e, component in product((3, 5, 6, 10, 15), (1, 2, 3, 5), (0, 1)):
            if gcd(e, q) > 1:
                continue
            direct, grouped = defaultdict(F), defaultdict(F)
            for n, u, v in product(range(1, 49), (-2, 1, 2), (-1, 1)):
                numerator = ((n+e*u)*(q+v)+u*v if component == 0
                             else n*v-e*q*u+u*v)
                weight = F(numerator, (n+1)*(e+1)*(q+1))
                for b, c in factor_pairs(n, 1, 6, 2):
                    if gcd(b*c, e*q) > 1 or gcd(n//(b*c), e) > 1:
                        continue
                    factor = mobius(e)*mobius(q)*mobius(b)*mobius(c)*weight
                    alpha = e*pow(b*c, -1, q) % q
                    for k, a in kernel_poly(q, alpha, n//(b*c), u, v).items():
                        direct[k] += factor*a
                if gcd(n, e) > 1:
                    continue
                factor = mobius(e)*mobius(q)*gamma(n, 1, 6, 2)*weight
                for k, a in kernel_poly(q, e, n, u, v).items():
                    grouped[k] += factor*a
            self.assertTrue(roots_equal([(F(k, q), a) for k, a in direct.items()],
                                        [(F(k, q), a) for k, a in grouped.items()]))

    def test_energy_reduction_is_not_large_sieve_length_reduction(self):
        B, conductor, G = 100, 3, 10
        correct = F(B, G)*(B+conductor**2)
        wrong = F(B, G)*(F(B, G)+conductor**2)
        self.assertGreater(correct, wrong)

    def test_all_four_physical_costs_and_threshold(self):
        self.assertEqual(physical_exponents(F(6, 5), F(1, 4)),
                         (F(-1, 40), F(27, 40), F(11, 40), F(39, 40)))
        self.assertEqual(max(physical_exponents(F(6, 5), F(1, 5))), 1)
        self.assertGreater(max(physical_exponents(F(6, 5), F(1, 6))), 1)
        self.assertEqual(max(physical_exponents(F(6, 5), 0))-
                         max(physical_exponents(F(6, 5), F(1, 4))), F(1, 8))

    def test_infinite_family_pattern_has_nonzero_merged_coefficient(self):
        # For n=g^2*p*r, a lower bound between g and g*min(p,r)
        # forces the two free primes into the two distinct factors.
        for g, p, r in ((2, 3, 5), (3, 5, 7), (5, 7, 11), (5, 7, 59)):
            n = g*g*p*r
            self.assertEqual(gamma(n, g, n//2, g), 2)

    def test_original_expanded_support_with_prime_modulus(self):
        e, q, b, c, m = 101, 103, 35, 55, 7
        n = b*c*m
        R = S = e*q
        N = 8*S
        T = N**(1/3)
        H = L = S/T**.5
        u = ceil(H/e)
        x = 3*T**.5/4
        y = (x*n+e*u)/S
        self.assertEqual(gcd(b, c), 5)
        self.assertGreaterEqual(5, T**.25)
        self.assertGreater(b*c, e)
        self.assertEqual(gcd(n, e*q), 1)
        self.assertEqual(gcd(u, q), 1)
        self.assertEqual(mobius(n), 0)
        self.assertTrue(R/2 <= n <= 2*R and n <= N/2 and S <= N/2)
        self.assertTrue(H <= e*u <= 2*H and L <= e*u <= 2*L)
        self.assertTrue(T**.5/2 <= y <= 2*T**.5)
        self.assertGreater(min(b, c), isqrt(e))
        self.assertGreaterEqual(min(q*b*c/R, q*e/H), 1)
        self.assertNotEqual(triple_spectrum(q, e*pow(b*c, -1, q) % q, 1, 1, 1), 0)
        self.assertNotEqual(gamma(n, isqrt(e), e, 2), 0)


if __name__ == '__main__':
    unittest.main()
