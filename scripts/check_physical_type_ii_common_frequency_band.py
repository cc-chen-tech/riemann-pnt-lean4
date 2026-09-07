#!/usr/bin/env python3
"""Exact guards for the common-frequency band, not an analytic gate proof."""
from fractions import Fraction as F
from math import gcd, floor, isqrt
from itertools import product
from collections import defaultdict
import unittest

from check_physical_type_i_triple_completion import triple_spectrum
from check_physical_large_gcd_type_columns import mobius, phi
from check_physical_squarefree_type_descent import divisors
from check_physical_centered_conductor_split import roots_equal


def projected_spectrum(q, r, alpha, k, u, v):
    ell = q//r
    if ell == 1:
        return F(0)
    return mobius(r)*phi(r)**2*triple_spectrum(
        ell,alpha*pow(r,-1,ell)%ell,k,u,v)


def band_weight(r, cutoff):
    return sum(mobius(r//g) for g in divisors(r) if g >= cutoff)


def gamma_column(n, r, lower_b=0, lower_c=0):
    return sum(mobius(b)*mobius(c) for b in divisors(n)
               for c in divisors(n//b)
               if b>lower_b and c>lower_c and gcd(b*c,r)==1)


def physical_exponents(eta, gamma):
    eta, gamma = F(eta), F(gamma)
    # Physical R=S=T^3 are NOT replaced with E(Q/G).
    return ((eta-1-gamma)/2, 2-eta-gamma/2,
            1-eta/2-3*gamma/2, F(7,2)-2*eta-3*gamma/2)


def kernel_poly(q, alpha, z, u, v):
    value = defaultdict(F)
    if q == 1 or gcd(z*u*v,q) != 1:
        return value
    value[-alpha*u*v*pow(z,-1,q)%q] += 1
    value[0] -= F(mobius(q),phi(q))
    return value


def projected_poly(q, r, alpha, z, u, v):
    ell = q//r
    value = defaultdict(F)
    if ell == 1:
        return value
    scalar = F(mobius(r)*phi(r)**2,r**3)
    for power, coeff in kernel_poly(ell,alpha*pow(r,-1,ell)%ell,z,u,v).items():
        value[r*power] += scalar*coeff
    return value


class BandTests(unittest.TestCase):
    def test_crt_inverse_divisor_changes_the_sign(self):
        self.assertEqual(projected_spectrum(6,2,1,-2,-2,-2),F(-9,2))

    def test_disjoint_layers_have_signed_not_positive_weights(self):
        self.assertEqual(band_weight(6,2),-1)

    def test_gamma_keeps_n_nonunit_at_projected_prime(self):
        self.assertEqual(gamma_column(4,2),1)

    def test_actual_four_costs_keep_physical_R_and_S(self):
        self.assertEqual(physical_exponents(F(6,5),F(1,10)),
                         (F(1,20),F(3,4),F(1,4),F(19,20)))

    def test_exact_spectrum_descent_including_zero_and_nonunit_coordinates(self):
        for q in (2,3,6,10,15,21,30,35):
            for r in divisors(q):
                for alpha in (1,q-1):
                    for k,u,v in product((-2,-1,0,1,2),repeat=3):
                        self.assertEqual(projected_spectrum(q,r,alpha,k,u,v),
                            triple_spectrum(q,alpha,r*k,r*u,r*v))

    def test_level_one_is_zero_not_an_added_principal(self):
        for q in (2,3,6,15,30):
            self.assertEqual(projected_spectrum(q,q,1,1,2,3),0)

    def test_spectral_band_and_mobius_disjoint_reassembly(self):
        for q in (2,3,6,10,15,30):
            for cutoff in (F(1),F(3,2),F(3),F(6),F(31)):
                for k,u,v in product(range(4),repeat=3):
                    common = gcd(q,gcd(k,gcd(u,v)))
                    via_divisors = sum(band_weight(r,cutoff) for r in divisors(common))
                    self.assertEqual(via_divisors,int(common>=cutoff))

    def test_cutoff_one_is_identity_not_sum_of_all_positive_projections(self):
        self.assertEqual([band_weight(r,1) for r in (1,2,3,6)], [1,0,0,0])

    def test_prime_modulus_has_no_high_common_band(self):
        for q in (3,5,7):
            for k,u,v in product(range(q),repeat=3):
                if gcd(q,gcd(k,gcd(u,v))) >= 2:
                    self.assertEqual(triple_spectrum(q,1,k,u,v),0)

    def test_direct_finite_inverse_and_projected_kernel_with_all_masks(self):
        for q in (3,6,10):
            for cutoff in (F(3,2),F(3)):
                for z,u,v in ((0,1,1),(2,1,1),(1,2,3),(2,2,2),(1,1,1)):
                    fourier, crt = defaultdict(F), defaultdict(F)
                    for k,r,s in product(range(q),repeat=3):
                        if gcd(q,gcd(k,gcd(r,s))) >= cutoff:
                            fourier[-(k*z+r*u+s*v)%q] += (
                                triple_spectrum(q,1,k,r,s)/q**3)
                    for d in divisors(q):
                        for power, coeff in projected_poly(q,d,1,z,u,v).items():
                            crt[power%q] += band_weight(d,cutoff)*coeff
                    self.assertTrue(roots_equal(
                        [(F(k,q),a) for k,a in fourier.items()],
                        [(F(k,q),a) for k,a in crt.items()]))

    def test_projected_kernel_can_live_at_original_nonunits(self):
        # q=6, r=2, z=2 is not a q-unit; the projection must not be remasked.
        value = projected_poly(6,2,1,2,1,1)
        self.assertFalse(roots_equal([(F(k,6),a) for k,a in value.items()],[]))
        self.assertEqual(kernel_poly(6,1,2,1,1),{})

    def test_full_gcd_ie_preserves_common_gamma_and_no_t_f_mask(self):
        for r in (2,3,5,6):
            for e in range(1,25):
                if not mobius(e) or gcd(e,r)>1:
                    continue
                for n in range(1,41):
                    gamma = gamma_column(n,r,1,1)
                    lhs = mobius(e)*gamma*int(gcd(e,n)==1)
                    rhs = sum(mobius(f)**2*mobius(e//f)*gamma
                              for f in divisors(gcd(e,n)) if gcd(e//f,f)==1)
                    self.assertEqual(lhs,rhs)

    def test_false_t_f_mask_deletes_a_necessary_ie_term(self):
        e,n,r = 2,4,3
        gamma = gamma_column(n,r,1,1)
        self.assertEqual(gamma,1)
        correct = sum(mobius(f)**2*mobius(e//f)*gamma for f in divisors(gcd(e,n)))
        wrong = sum(mobius(f)**2*mobius(e//f)*gamma
                    for f in divisors(gcd(e,n)) if gcd(n//f,f)==1)
        self.assertEqual((correct,wrong),(0,-1))

    def test_original_d_sum_and_B_masks_reassemble_before_second_ie(self):
        for r,e,n in product((2,3,5),range(1,16),range(1,31)):
            if gcd(e,r)>1 or not mobius(e):
                continue
            left = 0
            for b in divisors(n):
                for c in divisors(n//b):
                    if b<=1 or c<=1 or gcd(b*c,e*r)>1:
                        continue
                    left += mobius(e)*mobius(b)*mobius(c)*sum(
                        mobius(d) for d in divisors(gcd(n//(b*c),e)))
            right = mobius(e)*gamma_column(n,r,1,1)*int(gcd(n,e)==1)
            self.assertEqual(left,right)

    def test_gamma_is_divisor_bounded_even_without_squarefree_n(self):
        for n,r in product(range(1,101),(2,3,6,10)):
            tau3 = sum(len(divisors(n//b)) for b in divisors(n))
            self.assertLessEqual(abs(gamma_column(n,r)),tau3)

    def test_modulus_sign_fuses_once_with_projector(self):
        for r,ell in ((2,3),(3,5),(6,5),(5,7)):
            self.assertEqual(mobius(r*ell)*F(mobius(r)*phi(r)**2,r**3),
                             mobius(ell)*F(phi(r)**2,r**3))

    def test_dilation_of_quotient_keeps_frequency_gcd(self):
        for q,d,k,u,v in product((6,10,15),(1,7,11),range(6),range(4),range(4)):
            if gcd(q,d)==1:
                self.assertEqual(gcd(q,gcd(d*k,gcd(u,v))),gcd(q,gcd(k,gcd(u,v))))

    def test_common_divisor_count_does_not_pay_extra_modulus_count(self):
        for Q,r in product(range(2,31),range(1,61)):
            actual = sum(q%r==0 for q in range(Q,2*Q))
            self.assertLessEqual(actual,F(2*Q,r))
        for cutoff in (F(1),F(3,2),F(5),F(17,2)):
            for power in (F(3,2),F(5,2)):
                # Finite partial sums sit below first-term-plus-integral bound.
                start = max(1,-(-cutoff.numerator//cutoff.denominator))
                partial = sum(n**(-float(power)) for n in range(start,10001))
                bound = (1+1/float(power-1))*float(cutoff)**float(1-power)
                self.assertLessEqual(partial,bound)

    def test_threshold_pays_target_but_original_full_bound_does_not(self):
        self.assertEqual(max(physical_exponents(F(6,5),F(1,15))),1)
        self.assertEqual(max(physical_exponents(F(6,5),0)),F(11,10))
        self.assertGreater(max(physical_exponents(F(6,5),F(1,20))),1)

    def test_balanced_cutoff_has_no_unpaid_small_II_strip(self):
        for E in (F(1),F(9,4),F(4),F(31,4),F(16)):
            u = isqrt(floor(E))
            self.assertLessEqual(u*u,E)
            self.assertGreater((u+1)**2,E)

    def test_original_integer_support_and_band_not_just_large_frequency_tail(self):
        e,r,ell,b,c,m = 101,5,103,29,31,59
        q,B = r*ell,b*c
        R=S=e*q; N=8*S; T=N**(1/3); H=L=S/T**.5
        n=B*m
        u=next(x for x in range(floor(H/e)+1,floor(H/e)+4) if gcd(x,q)==1)
        self.assertEqual(gcd(n,e*q),1)
        self.assertTrue(R/2<=n<=2*R and n<=N/2 and S<=N/2)
        self.assertTrue(H<=e*u<=2*H and L<=e*u<=2*L)
        self.assertGreater(min(b,c),isqrt(e))
        x=3*T**.5/4; y=(x*n+e*u)/S
        self.assertTrue(T**.5/2<=y<=2*T**.5)
        self.assertLessEqual(r,q*B/R)
        self.assertLessEqual(r,q*e/H)
        alpha=e*pow(B,-1,q)%q
        self.assertNotEqual(projected_spectrum(q,r,alpha,1,1,1),0)


if __name__ == '__main__':
    unittest.main()
