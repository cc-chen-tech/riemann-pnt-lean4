#!/usr/bin/env python3
"""Finite TTC guards; neither smooth Poisson nor the Type-II gate is tested."""
from fractions import Fraction as F
from collections import defaultdict
from itertools import product
from math import ceil, gcd, isqrt, sqrt
import unittest

from check_physical_large_gcd_type_columns import mobius, phi
from check_physical_squarefree_type_descent import divisors
from check_physical_centered_conductor_split import roots_equal


def triple_spectrum(q, alpha, k, r, s):
    if q < 1 or mobius(q) == 0 or gcd(alpha, q) != 1:
        raise ValueError('requires positive squarefree q and unit alpha')
    raw = principal = F(1)
    for p in (d for d in divisors(q) if d > 1 and phi(d) == d-1):
        def ram(n):
            return p-1 if n % p == 0 else -1
        raw *= p*ram(k+pow(alpha, -1, p)*r*s)*int(r % p != 0)-ram(k)*ram(s)
        principal *= F(-ram(k)*ram(r)*ram(s), p-1)
    return raw-principal


def type_i_exponents(eta, delta, beta=0):
    eta, delta, beta = map(F, (eta, delta, beta))
    m, q, r, s, h, ell = delta-eta, 3-delta, F(3), F(3), F(5, 2), F(5, 2)
    outer = 1-r-s+beta
    return outer+m+eta+2*q, outer+q+h+ell-eta


class TripleCompletionTests(unittest.TestCase):
    def test_invalid_modulus_or_nonunit_alpha_is_not_certified(self):
        for q, alpha in ((0, 1), (4, 1), (12, 5), (6, 2)):
            with self.assertRaises(ValueError):
                triple_spectrum(q, alpha, 1, 1, 1)

    def test_prime_nonresonance_keeps_principal_subtraction(self):
        self.assertEqual(triple_spectrum(5, 1, 1, 1, 1), F(-25, 4))

    def test_composite_nonunit_frequency_survives(self):
        self.assertEqual(triple_spectrum(6, 1, 2, 2, 2), F(-9, 2))

    def test_full_type_i_cost_with_growing_cutoffs(self):
        self.assertEqual(type_i_exponents(F(6, 5), F(6, 5), F(1, 5)), (F(0), F(4, 5)))

    def test_prime_resonance_is_not_treated_as_size_q(self):
        self.assertEqual(triple_spectrum(5, 1, -1, 1, 1), F(75, 4))

    def test_global_center_is_not_product_of_local_centers(self):
        self.assertEqual(triple_spectrum(15, 1, 1, 1, 1), F(191, 8))
        local_product = triple_spectrum(3, 1, 1, 1, 1)*triple_spectrum(5, 1, 1, 1, 1)
        self.assertEqual(local_product, F(225, 8))
        self.assertNotEqual(local_product, triple_spectrum(15, 1, 1, 1, 1))

    def test_three_complete_coordinate_planes_vanish(self):
        for q in (1, 2, 3, 6, 10, 15, 30):
            for a, b in product(range(q), repeat=2):
                for k, r, s in ((0, a, b), (a, 0, b), (a, b, 0)):
                    self.assertEqual(triple_spectrum(q, 1, k, r, s), 0)

    def test_exact_complete_dft_matches_crt_with_nonunit_frequencies(self):
        count = surviving_nonunit = 0
        frequencies = ((0,1,1),(1,0,1),(1,1,0),(1,1,1),(2,3,5),
                       (-1,2,3),(6,5,4),(2,2,2),(3,-1,5),(5,7,-2))
        for q in (1, 2, 3, 5, 6, 10, 15, 21, 30):
            units = [a for a in range(q) if gcd(a, q) == 1]
            for alpha in sorted(set((1, q-1))):
                if gcd(alpha, q) != 1:
                    continue
                for k, r, s in frequencies:
                    terms = defaultdict(F)
                    for z, x, y in product(units, repeat=3):
                        add = k*z+r*x+s*y
                        terms[(add-alpha*x*y*pow(z, -1, q)) % q] += 1
                        terms[add % q] -= F(mobius(q), phi(q))
                    expected = triple_spectrum(q, alpha, k, r, s)
                    self.assertTrue(roots_equal([(F(a, q), v) for a, v in terms.items()],
                                                [(F(0), expected)]))
                    surviving_nonunit += int(gcd(k*r*s, q) > 1 and expected != 0)
                    count += 1
        self.assertEqual(count, 170)
        self.assertEqual(surviving_nonunit, 28)

    def test_gcd_spectrum_bound_including_inactive_crt_factors(self):
        for q in range(1, 43):
            if mobius(q) == 0:
                continue
            for k, r, s in product(range(-2, 4), repeat=3):
                val = triple_spectrum(q, 1, k, r, s)
                self.assertLessEqual(abs(val), (len(divisors(q))+1)*q*gcd(q, k+r*s))

    def test_nonzero_product_incidence_pays_integer_remainder(self):
        checks = 0
        for q, alpha, K, R, S in product((2,6,15,30),(1,7),(1,2,3),(1,2,4),(1,3,5)):
            if gcd(alpha, q) != 1:
                continue
            rr, ss = list(range(-R, 0))+list(range(1, R+1)), list(range(-S, 0))+list(range(1, S+1))
            tmax = max(len(divisors(n)) for n in range(1, R*S+1))
            for k in range(-K, K+1):
                if k == 0:
                    continue
                actual = sum(gcd(q, alpha*k+r*s) for r, s in product(rr, ss))
                expanded = sum(phi(d)*sum((alpha*k+r*s) % d == 0 for r, s in product(rr, ss))
                               for d in divisors(q))
                budget = 4*tmax*sum(phi(d)*(R*S//d+1) for d in divisors(q))
                self.assertEqual(actual, expanded)
                self.assertLessEqual(actual, budget)
                checks += 1
        self.assertEqual(checks, 864)

    def test_product_zero_is_not_a_divisor_counted_integer(self):
        pairs = [(r, s) for r, s in product(range(-9, 10), repeat=2) if r*s == 0]
        self.assertEqual(len(pairs), 37)
        self.assertGreater(len(pairs), 2*len(divisors(1)))
        self.assertEqual(triple_spectrum(15, 1, 1, 0, 7), 0)

    def test_full_three_masks_reassemble_without_z_d_mask(self):
        for A, e, a0, b0, q in ((1, 6, 1, 1, 5), (6, 5, 2, 3, 7), (30, 7, 3, 5, 11)):
            for m, u, v in product(range(1, 12), range(-3, 4), range(-3, 4)):
                if u*v == 0:
                    continue
                direct = int(gcd(m, A*e*q) == gcd(u, b0*q) == gcd(v, a0*q) == 1)
                expanded = sum(
                    mobius(d)*mobius(j)*mobius(ell)
                    for d, j, ell in product(divisors(A*e), divisors(b0), divisors(a0))
                    if m % d == u % j == v % ell == 0 and gcd((m//d)*(u//j)*(v//ell), q) == 1)
                self.assertEqual(direct, expanded)
        # m=4,d=2,z=2 is a necessary IE summand, not a unit z,d pair.
        self.assertEqual(gcd(4//2, 2), 2)

    def test_complete_signed_type_i_with_joint_rational_weight(self):
        fixtures = ((1,1,1,2,5,12),(2,3,1,5,7,18),(3,1,2,5,7,18),
                    (1,1,1,5,6,15),(1,1,1,7,15,14),(1,1,1,2,1,10))
        labels = (-3,-2,-1,1,2,3)
        for a0, b0, q0, e, q, R in fixtures:
            A = q0*a0*b0
            direct, joined = defaultdict(F), defaultdict(F)
            def add(out, phase, coeff):
                out[phase % q] += coeff
                out[0] -= coeff*F(mobius(q), phi(q))
            for b, c in product(range(1, 4), repeat=2):
                B = b*c
                common = -mobius(a0)*mobius(b0)*mobius(e)*mobius(q)*mobius(b)*mobius(c)
                if not common or gcd(B, A*e*q) != 1:
                    continue
                for n, u, v in product(range(R, 2*R), labels, labels):
                    if n % B:
                        continue
                    weight = F((n+e+u*v)**2, (1+e*n)**2)
                    if gcd(n//B, A*e*q) == gcd(u, b0*q) == gcd(v, a0*q) == 1:
                        add(direct, -e*u*v*pow(n, -1, q), common*weight)
                    for d, j, ell in product(divisors(A*e), divisors(b0), divisors(a0)):
                        if n % (B*d) or u % j or v % ell:
                            continue
                        z, x, y = n//(B*d), u//j, v//ell
                        if gcd(z*x*y, q) != 1:
                            continue
                        coeff = common*mobius(d)*mobius(j)*mobius(ell)
                        alpha = e*j*ell*pow(B*d, -1, q)
                        add(joined, -alpha*x*y*pow(z, -1, q), coeff*weight)
            self.assertTrue(all(direct[k] == joined[k] for k in set(direct)|set(joined)))

    def test_shared_short_factors_and_unsigned_square_quotient_remain(self):
        # For n=4,U=V=1, I=-1 and II contains (b,c,m)=(2,2,1).
        self.assertEqual(-1+mobius(2)**2, mobius(4))
        self.assertNotEqual(-1, mobius(4))
        self.assertEqual(gcd(2, 2), 2)

    def test_original_cutoff_boundary_is_exact(self):
        for n, U, V in product(range(1, 61), (1,2,4), (1,3)):
            short = long = 0
            for b in divisors(n):
                for c in divisors(n//b):
                    if b <= U and c <= V:
                        short += mobius(b)*mobius(c)
                    if b > U and c > V:
                        long += mobius(b)*mobius(c)
            boundary = mobius(n)*(int(n <= U)+int(n <= V))
            self.assertEqual(mobius(n), -short+long+boundary)

    def test_joint_weight_scaling_has_no_divisor_derivative_factor(self):
        for a0, b0, e, q, B, d, j, ell in ((2,3,5,7,4,6,3,2), (1,1,7,15,4,7,1,1)):
            R, S, H, L = 100, a0*b0*e*q, 91, 103
            Z, X, Y = F(R, B*d), F(H, a0*e*j), F(L, b0*e*ell)
            z, x, y = Z*F(3,2), X*F(-2,3), Y*F(4,3)
            coords = (F(B*d, R)*z, F(a0*b0*e*q, S), F(b0*e*ell, L)*y, F(a0*e*j, H)*x)
            self.assertEqual(coords, (F(3,2), F(1), F(4,3), F(-2,3)))

    def test_extra_mobius_on_quotient_breaks_the_zero_plane(self):
        q = 5
        plain = []; weighted = []
        for z in range(1, q):
            pair = [(F(-pow(z,-1,q), q), F(1)), (F(0), -F(mobius(q), phi(q)))]
            plain += pair
            weighted += [(phase, value*mobius(z)) for phase, value in pair]
        self.assertTrue(roots_equal(plain, []))
        self.assertFalse(roots_equal(weighted, []))

    def test_nonzero_dyadic_sampling_retains_small_scale_cubic_gain(self):
        for scale in (F(1,100), F(1,4), F(1), F(3), F(20)):
            finite = sum((F(2**j)/(1+F(2**j)/scale)**4 for j in range(32)), F(0))
            self.assertLessEqual(finite, 4*scale*min(F(1), scale**3))

    def test_all_frequency_cutoff_tail_has_integrable_majorant(self):
        for ratio, K in product((F(1,8), F(1), F(3)), (1,4,11)):
            finite = sum(((1+k*ratio)**(-4) for k in range(K+1,K+101)), F(0))
            self.assertLessEqual(finite, 1/(3*ratio*(1+K*ratio)**3))

    def test_outer_counts_include_canonical_allocations_and_full_q_shell(self):
        for A, B, E, Q in ((1,1,2,3), (2,3,5,7), (5,7,11,13)):
            first = sum(q for _a, _b, _e, q in product(range(A,2*A),range(B,2*B),range(E,2*E),range(Q,2*Q)))
            self.assertLessEqual(first, 2*A*B*E*Q**2)
            second = sum((F(1,a*b*e*e) for a,b,e,_q in product(
                range(A,2*A),range(B,2*B),range(E,2*E),range(Q,2*Q))), F(0))
            self.assertLessEqual(second, F(Q,E))

    def test_type_ii_is_nonempty_after_short_cutoffs(self):
        U = V = 3
        b, c, m = 5, 7, 11
        self.assertTrue(b > U and c > V)
        self.assertNotEqual(mobius(b)*mobius(c), 0)
        self.assertGreater(b*c*m, max(U,V))

    def test_actual_original_support_and_growing_cutoff_witness(self):
        e, q = 101, 1009
        S = R = e*q
        T = (8*S)**(1/3)
        H = L = S/sqrt(T)
        u = v = ceil(H/e)
        def prime(n):
            return n >= 2 and all(n % a for a in range(2, isqrt(n)+1))
        n = next(n for n in range(S+1, 2*S) if prime(n))
        cutoff = int(T**.1)
        self.assertTrue(1 <= cutoff < R/2)
        self.assertTrue(H <= e*u <= 2*H and L <= e*v <= 2*L)
        self.assertEqual(gcd(n*u*v, e*q), 1)
        y = (3*sqrt(T)*n/4+e*v)/S
        self.assertTrue(sqrt(T)/2 <= y <= 2*sqrt(T))


if __name__ == '__main__':
    unittest.main()
