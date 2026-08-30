#!/usr/bin/env python3
"""Finite hyperbolic guards; they do not certify analytic tails or the gate."""
from fractions import Fraction as F
from math import gcd, floor, ceil, sqrt
from itertools import product
from collections import defaultdict
import unittest

from check_physical_type_i_triple_completion import triple_spectrum
from check_physical_large_gcd_type_columns import mobius, phi
from check_physical_squarefree_type_descent import divisors
from check_physical_centered_conductor_split import roots_equal


def representation_count(n):
    if n == 0:
        return 0
    n = abs(n)
    return 2*sum(len(divisors(n//b//c)) for b in divisors(n)
                 for c in divisors(n//b))


def physical_exponents(eta, beta):
    eta, beta = F(eta), F(beta)
    r = s = F(3)
    h = ell = F(5,2)
    q = 3-eta
    return (1+h+ell+q-r-s-eta,
            1+beta+eta+2*q-r-s,
            1+beta+q+h+ell-2*r-s)


def nz_box(length):
    return tuple(n for n in range(-floor(length),floor(length)+1) if n)


def gcd_box(q, a, D, K, R, S):
    """Direct nonzero-integer-determinant count and its exact totient expansion."""
    direct = expanded = 0
    for b in range(1,2*D):
        for c in range(1,2*D):
            if not D <= b*c < 2*D or gcd(b*c,a*q) != 1:
                continue
            for k,r,s in product(nz_box(K),nz_box(R),nz_box(S)):
                delta = a*k+b*c*r*s
                if delta:
                    direct += gcd(q,delta)
                    expanded += sum(phi(v) for v in divisors(q) if delta%v == 0)
    return direct, expanded


def finite_majorant(q, a, D, K, R, S):
    nmax = floor(2*D*R*S)
    if nmax < 1:
        return F(0)
    tau4max = max(representation_count(n)//2 for n in range(1,nmax+1))
    delta_max = a*K+2*D*R*S
    return 8*tau4max*K*delta_max*sum(F(phi(v),v) for v in divisors(q))


class HyperbolicTests(unittest.TestCase):
    def test_zero_rhs_has_no_nonzero_four_factor_representation(self):
        self.assertEqual(representation_count(0), 0)

    def test_negative_rhs_retains_both_label_sign_choices(self):
        self.assertEqual(representation_count(-6), 32)

    def test_all_three_original_normalized_costs(self):
        self.assertEqual(physical_exponents(F(6,5),F(11,10)),
                         (F(3,5),F(9,10),F(-1,10)))

    def test_endpoint_short_product_has_target_scale(self):
        self.assertEqual(physical_exponents(F(6,5),F(6,5)),
                         (F(3,5),F(1),F(0)))

    def test_four_factor_formula_matches_signed_enumeration(self):
        for n in range(-32,33):
            brute = 0
            if n:
                for b in range(1,abs(n)+1):
                    for c in range(1,abs(n)//b+1):
                        for r in nz_box(F(abs(n),b*c)):
                            brute += int(n%(b*c*r) == 0)
            self.assertEqual(representation_count(n),brute)

    def test_totient_expansion_and_joint_not_per_bc_majorant(self):
        count = 0
        for q,a,D,K,R,S in product((2,3,6,10,15),(1,2,3),(1,2,4),
                                   (F(1,2),F(1),F(2)),(F(1,2),F(2)),(F(2),)):
            if gcd(a,q) != 1:
                continue
            lhs, expanded = gcd_box(q,a,D,K,R,S)
            self.assertEqual(lhs,expanded)
            self.assertLessEqual(lhs,finite_majorant(q,a,D,K,R,S))
            count += 1
        self.assertGreater(count,150)

    def test_subunit_nonzero_frequency_boxes_are_empty_without_plus_one(self):
        for K,R,S in ((F(1,8),3,5),(2,F(1,2),2),(4,4,F(3,4))):
            self.assertEqual(gcd_box(30,1,4,K,R,S),(0,0))
        self.assertEqual(finite_majorant(6,1,1,F(1,4),F(1,4),F(1,4)),0)
        for L in (F(1,16),F(3,4),F(1),F(9,4)):
            self.assertLessEqual(len(nz_box(L)),2*L)

    def test_zero_rhs_pairs_are_not_passed_to_divisor_count(self):
        q,a,k,j,v = 6,2,3,1,6
        self.assertEqual(v*j-a*k,0)
        self.assertNotEqual(j,0)
        self.assertEqual(representation_count(v*j-a*k),0)
        self.assertGreater(gcd(q,a*k),0)

    def test_integer_resonance_not_modular_resonance_is_excluded(self):
        # q | Delta but Delta != 0 belongs in the new nonzero count.
        a,b,c,k,r,s,q = 1,1,1,5,1,1,6
        delta = a*k+b*c*r*s
        self.assertEqual(delta,6)
        self.assertNotEqual(delta,0)
        self.assertEqual(gcd(q,delta),6)

    def test_complete_centered_spectrum_retains_constant_and_nonunit_terms(self):
        self.assertEqual(triple_spectrum(5,1,1,1,1),F(-25,4))
        self.assertEqual(triple_spectrum(6,1,2,2,2),F(-9,2))
        self.assertEqual(triple_spectrum(5,1,-1,1,1),F(75,4))

    def test_full_spectrum_bound_and_three_zero_planes(self):
        nonunit = 0
        for q in (1,2,3,6,10,15,30,35):
            for a,B in ((1,1),(2,7),(7,11)):
                if gcd(a*B,q) != 1:
                    continue
                alpha = a*pow(B,-1,q)%q
                for k,r,s in product((-2,-1,0,1,2),repeat=3):
                    value = triple_spectrum(q,alpha,k,r,s)
                    bound = (len(divisors(q))+1)*q*gcd(q,a*k+B*r*s)
                    self.assertLessEqual(abs(value),bound)
                    if k*r*s == 0:
                        self.assertEqual(value,0)
                    nonunit += bool(value and gcd(k*r*s,q)>1)
        self.assertGreater(nonunit,0)

    def test_full_dft_inverse_with_nonseparable_complex_weight(self):
        # Two rational components test a genuinely complex weight independently.
        for q in (3,6,10):
            for component in (0,1):
                direct, inverse = defaultdict(F), defaultdict(F)
                for z,u,v in ((1,1,1),(2,-1,3),(3,2,-1),(5,-2,1)):
                    w = F(z*u+v*z*z if component == 0 else z-v*u*u,
                          1+z*z+u*u+v*v)
                    if gcd(z*u*v,q) == 1:
                        direct[F(-u*v*pow(z,-1,q),q)%1] += w
                        direct[0] -= w*F(mobius(q),phi(q))
                    for k,r,s in product(range(q),repeat=3):
                        inverse[F(-k*z-r*u-s*v,q)%1] += (
                            w*triple_spectrum(q,1,k,r,s)/q**3)
                self.assertTrue(roots_equal(list(direct.items()),list(inverse.items())))

    def test_all_divisor_resonances_have_k_multiple_of_B(self):
        for e,B in ((6,5),(10,3),(21,2),(35,6)):
            for d in divisors(e):
                a = e//d
                for k,r,s in product(nz_box(12),nz_box(6),nz_box(6)):
                    if a*k+B*r*s == 0:
                        self.assertEqual(k%B,0)
                        self.assertEqual(r*s,-a*(k//B))
                        self.assertNotEqual(k//B,0)

    def test_no_coprimality_between_b_and_c_can_be_inserted(self):
        b = c = 2
        e,q,m = 3,5,7
        self.assertEqual(gcd(b*c,e*q),1)
        self.assertEqual(mobius(b)*mobius(c),1)
        self.assertEqual(mobius(b*c*m),0)
        self.assertGreater(gcd(b,c),1)

    def test_original_unit_ie_cancels_nonsquarefree_quotients_correctly(self):
        for e,B,m in product((2,3,6,10),(1,7,11),range(1,25)):
            if gcd(B,e) != 1:
                continue
            self.assertEqual(sum(mobius(d) for d in divisors(e) if m%d==0),
                             int(gcd(m,e)==1))
        # z may share a or d after IE; these are not new masks.
        wrong = sum(mobius(d) for d in divisors(6) if gcd(6//d,6)==1)
        self.assertEqual(wrong,1)
        self.assertNotEqual(wrong,int(gcd(6,6)==1))

    def test_normalized_shell_two_terms_without_extra_B_count(self):
        for e,d,D,q,R,H,L in ((30,6,4,7,210,35,42),
                              (35,7,3,6,210,70,21),(6,6,8,35,210,21,70)):
            a = F(e,d)
            K = F(q*D*d,R)
            lr,ls = F(q*e,H),F(q*e,L)
            pref = F(R*H*L,D*d*e*e*q*q)
            self.assertEqual(pref*K*a*K,F(D*H*L,e*R))
            self.assertEqual(pref*K*D*lr*ls,D*q)

    def test_dyadic_tail_geometric_growth_is_summable_at_J4(self):
        # eps=1/4 is sufficient; these rational powers bound the growth.
        for ak,ar,ass in product(range(10),repeat=3):
            resonance_growth = 2**(2*ak)
            nonzero_growth = 2**(ak+2*ar+2*ass)
            decay = F(1,2**(4*(ak+ar+ass)))
            self.assertLessEqual(decay*resonance_growth,
                                 F(1,2**(2*ak+2*ar+2*ass)))
            self.assertLessEqual(decay*nonzero_growth,
                                 F(1,2**(2*ak+2*ar+2*ass)))

    def test_balanced_gain_and_explicit_unpaid_long_product(self):
        eta,beta = F(6,5),F(11,10)
        old = (1+beta+eta+2*(3-eta)-6,
               1+beta+(3-eta)+5-eta-6)
        self.assertEqual(old,(F(9,10),F(17,10)))
        self.assertEqual(max(old)-max(physical_exponents(eta,beta)),F(4,5))
        self.assertGreater(max(physical_exponents(eta,F(13,10))),1)

    def test_composite_physical_integer_support_and_mobius_sign(self):
        # Full actual support, not a positivity claim about an arbitrary Psi.
        e,q,b,c,m = 101,7*11,3,17,163
        S = R = e*q
        N = 8*S
        T = N**(1/3)
        H = L = S/sqrt(T)
        B,n = b*c,b*c*m
        u = next(j for j in range(ceil(H/e),ceil(H/e)+3) if gcd(j,q)==1)
        v = u
        self.assertEqual(mobius(q),1)
        self.assertLess(R,n)
        self.assertLess(n,2*R)
        self.assertLessEqual(n,N/2)
        self.assertEqual(gcd(n,e*q),1)
        self.assertEqual(gcd(u*v,q),1)
        self.assertEqual(gcd(S,gcd(e*u,e*v)),e)
        self.assertTrue(H<=e*u<=2*H and L<=e*v<=2*L)
        self.assertLess(B,T**(11/10))
        self.assertGreater(B,T**(7/10))
        self.assertGreater(min(b,c),floor(T**(1/10)))
        x = 3*sqrt(T)/4
        y = (x*n+e*v)/S
        self.assertTrue(sqrt(T)/2<=y<=2*sqrt(T))


if __name__ == '__main__':
    unittest.main()
