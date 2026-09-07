#!/usr/bin/env python3
"""Exact near-prime guards; no certification of analytic Poisson tails."""
from fractions import Fraction as F
from math import gcd, isqrt, ceil, sqrt
from itertools import product
from collections import defaultdict
import unittest

from check_physical_type_i_triple_completion import triple_spectrum
from check_physical_large_gcd_type_columns import mobius, phi
from check_physical_squarefree_type_descent import divisors
from check_physical_centered_conductor_split import roots_equal


def crt_branches(ell, p, alpha, k, r, s):
    if (ell < 1 or not mobius(ell) or p < 2 or
            any(p % j == 0 for j in range(2,isqrt(p)+1)) or
            gcd(ell,p) != 1 or gcd(alpha,ell*p) != 1):
        raise ValueError('coprime squarefree ell, prime p and unit alpha required')
    def principal(t):
        def ram(v):
            return sum(d*mobius(t//d) for d in divisors(t) if v%d==0)
        return F(mobius(t),phi(t))*ram(k)*ram(r)*ram(s)
    hell = triple_spectrum(ell,alpha,k,r,s)
    rell = hell+principal(ell)
    return (rell*triple_spectrum(p,alpha,k,r,s),hell*principal(p))


def near_prime_tags(q, cap):
    if q < 2 or cap < 1 or cap*cap >= q or not mobius(q):
        return []
    return [(ell,q//ell) for ell in range(1,int(cap)+1) if q%ell==0 and q//ell>=2
            and all((q//ell)%j for j in range(2,isqrt(q//ell)+1))]


def physical_exponents(eta, beta, gamma, omega, J):
    eta,beta,gamma,omega=map(F,(eta,beta,gamma,omega))
    r=s=F(3)
    h=ell=F(5,2)
    q=3-eta
    return (1-r-s+h+ell+q-eta,
            1-r-s+h+ell+2*gamma,
            1-r-s+eta+3*q+beta-(J-1)*omega,
            1+h+ell+gamma-s-eta+J*(gamma+eta-h))


class NearPrimeTests(unittest.TestCase):
    def test_nonunit_q_high_branch_is_not_removed(self):
        self.assertEqual(crt_branches(2,3,1,2,2,2),(F(-9,2),F(0)))

    def test_p_divisible_frequency_retains_low_branch(self):
        self.assertEqual(crt_branches(3,5,1,5,1,1),(F(0),F(-9,2)))

    def test_large_prime_tag_is_unique_in_the_admitted_family(self):
        self.assertEqual(near_prime_tags(105,4),[])
        self.assertEqual(near_prime_tags(231,7),[])
        self.assertEqual(near_prime_tags(1155,40),[])
        self.assertEqual(near_prime_tags(303,4),[(3,101)])

    def test_all_four_physical_costs_are_present(self):
        self.assertEqual(physical_exponents(F(6,5),F(3,5),F(1,10),F(1,25),48),
                         (F(3,5),F(1,5),F(8,25),F(-557,10)))

    def test_crt_branches_match_full_spectrum_not_product_of_centers(self):
        count=nonunit=low=0
        for ell,p in ((1,3),(2,3),(3,5),(6,5),(10,7),(15,7),(21,11)):
            q=ell*p
            for alpha in (1,q-1):
                for k,r,s in product((-p,-2,-1,0,1,2,p),repeat=3):
                    hi,lo=crt_branches(ell,p,alpha,k,r,s)
                    self.assertEqual(hi+lo,triple_spectrum(q,alpha,k,r,s))
                    nonunit+=bool(hi and gcd(k*r*s,q)>1)
                    low+=bool(lo and k%p==0)
                    count+=1
        self.assertEqual(count,4802)
        self.assertGreater(nonunit,0)
        self.assertGreater(low,0)
        self.assertNotEqual(triple_spectrum(15,1,1,1,1),
                            triple_spectrum(3,1,1,1,1)*triple_spectrum(5,1,1,1,1))

    def test_invalid_crt_inputs_are_rejected(self):
        for args in ((4,5,1),(3,3,1),(3,9,1),(3,5,3),(0,5,1)):
            with self.assertRaises(ValueError):
                crt_branches(*args,1,1,1)

    def test_scaled_physical_crt_with_nonseparable_rational_weights(self):
        for ell,p in ((1,3),(2,3),(3,5),(6,5)):
            q=ell*p
            direct,split=defaultdict(F),defaultdict(F)
            for z,u,v in product(range(1,q+2),(-3,-1,1,2,5),(-2,-1,1,3)):
                if gcd(z*u*v,q)!=1:
                    continue
                w=F(z*u+v*z*z,1+z*z+u*u+v*v)
                direct[F(-u*v*pow(z,-1,q),q)%1]+=w
                direct[0]-=w*F(mobius(q),phi(q))
                ae=pow(p,-1,ell)
                ap=pow(ell,-1,p)
                phasee=F(-ae*u*v*pow(z,-1,ell),ell)
                phasep=F(-ap*u*v*pow(z,-1,p),p)
                split[(phasee+phasep)%1]+=w
                split[phasee%1]+=w*F(1,p-1)
                split[phasee%1]-=w*F(1,p-1)
                split[0]+=w*F(mobius(ell),phi(ell)*(p-1))
            self.assertTrue(roots_equal(list(direct.items()),list(split.items())))

    def test_physical_alpha_cannot_drop_complement_inverse(self):
        ell,p,z,u,v=3,5,1,1,1
        correct=[(F(-pow(p,-1,ell)*u*v*pow(z,-1,ell),ell),F(1))]
        wrong=[(F(-u*v*pow(z,-1,ell),ell),F(1))]
        self.assertFalse(roots_equal(correct,wrong))

    def test_high_constant_full_inverse_has_no_extra_cofactor(self):
        for ell,p in ((1,3),(2,3),(3,5),(6,5)):
            q=ell*p
            for z,u,v in ((1,1,1),(2,-1,3),(p,p,1),(ell,1,2)):
                spectral=defaultdict(F)
                for k,r,s in product(range(q),repeat=3):
                    if gcd(k*r*s,p)!=1:
                        continue
                    hell=triple_spectrum(ell,1,k,r,s)
                    ram=lambda n:sum(t*mobius(ell//t) for t in divisors(ell) if n%t==0)
                    rell=hell+F(mobius(ell),phi(ell))*ram(k)*ram(r)*ram(s)
                    spectral[F(-k*z-r*u-s*v,q)%1]-=F(p*p,q**3*(p-1))*rell
                direct=[]
                if gcd(z*u*v,ell)==1:
                    rp=lambda n:p-1 if n%p==0 else -1
                    phase=F(-pow(p,-1,ell)*u*v*pow(z,-1,ell),ell)
                    direct=[(phase,F(-rp(z)*rp(u)*rp(v),p*(p-1)))]
                self.assertTrue(roots_equal(list(spectral.items()),direct))

    def test_low_kernel_complete_u_period_is_exactly_centered(self):
        for ell in (1,2,3,6,10,15,30):
            for alpha,z,v in ((1,1,1),(7,11,13),(11,7,-1)):
                if gcd(alpha*z*v,ell)!=1:
                    continue
                terms=[(F(-alpha*u*v*pow(z,-1,ell),ell),F(1))
                       for u in range(ell) if gcd(u,ell)==1]
                terms.append((F(0),F(-mobius(ell))))
                self.assertTrue(roots_equal(terms,[]))

    def test_p_unit_mask_is_not_generally_redundant(self):
        ell,p=3,5
        unmasked,masked=[],[]
        for u in range(4,7):
            if gcd(u,ell)!=1:
                continue
            terms=[(F(-u,ell),F(1)),(F(0),F(1,2))]
            unmasked+=terms
            if u%p:
                masked+=terms
        self.assertTrue(roots_equal(unmasked,[]))
        self.assertFalse(roots_equal(masked,[]))

    def test_displayed_small_label_support_makes_only_u_mask_redundant(self):
        p,X=101,F(23,2)
        self.assertLess(2*X,p)
        self.assertTrue(all(gcd(u,p)==1 for u in range(-int(2*X),int(2*X)+1) if u))
        self.assertNotEqual(gcd(p,p),1)  # z or v may still equal p.

    def test_unique_tag_count_does_not_pay_cofactor_twice(self):
        for Q,cap in ((20,3),(100,7),(500,17)):
            tagged=[(q,t) for q in range(Q,2*Q) for t in near_prime_tags(q,cap)]
            self.assertEqual(len({q for q,t in tagged}),len(tagged))
            weight=sum((F(1,p) for q,(ell,p) in tagged),F(0))
            self.assertLessEqual(weight,cap*sum((F(1,q) for q in range(Q,2*Q)),F(0)))
        self.assertEqual(near_prime_tags(303,4),[(3,101)])
        self.assertEqual(near_prime_tags(909,4),[])  # nonsquarefree q.

    def test_prime_gap_does_not_serve_as_large_prime_factor_gap(self):
        q,ell,p,delta=15,3,5,5
        self.assertLess(delta,q)
        self.assertEqual(delta%p,0)
        self.assertNotEqual(delta,0)
        self.assertGreater(delta,F(q,2*ell))

    def test_strengthened_gap_has_positive_power_margin(self):
        eta,beta,gamma,omega=F(6,5),F(3,5),F(1,10),F(1,25)
        self.assertEqual((3-eta)-(beta+1+2*omega+gamma),F(1,50))
        self.assertLess(2*gamma,3-eta)
        self.assertLess(F(5,2)-eta,3-eta-gamma)
        self.assertLess(gamma+eta,F(5,2))

    def test_high_derivative_tail_is_not_free(self):
        self.assertGreater(physical_exponents(F(6,5),F(3,5),F(1,10),F(1,25),4)[2],1)
        self.assertLess(physical_exponents(F(6,5),F(3,5),F(1,10),F(1,25),48)[2],F(3,5))

    def test_actual_composite_support_with_both_long_factors(self):
        e,ell,p,b,c,cap,Bmax,inflation=1009,3,1000000007,5,7,4,64,2
        q=ell*p
        S=R=e*q
        T=(8*S)**(1/3)
        H=L=S/sqrt(T)
        B=b*c
        m=ceil(R/B)
        while gcd(m,B*e*q)!=1 or not mobius(m):
            m+=1
        n=B*m
        u=ceil(H/e)
        if u%ell==0:
            u+=1
        v=u
        self.assertEqual(near_prime_tags(q,cap),[(ell,p)])
        self.assertTrue(b>int(T**.1) and c>int(T**.1) and B<=Bmax)
        self.assertTrue(R<=n<2*R and n<=8*S/4)
        self.assertEqual(gcd(n,e*q),1)
        self.assertEqual(gcd(u*v,q),1)
        self.assertEqual(gcd(gcd(S,e*u),e*v),e)
        self.assertNotEqual(mobius(n),0)
        self.assertLessEqual(Bmax*inflation**2*(4*e*q/R+16*e*e*q*q/(H*L)),q/(2*cap))
        self.assertLess(2*H/e,q/cap)
        self.assertLessEqual(2*cap*e/H,.5)
        y=(3*sqrt(T)*n/4+e*v)/S
        self.assertTrue(sqrt(T)/2<=y<=2*sqrt(T))

    def test_composite_growing_cofactor_family_exponents(self):
        e,ell,p,b,c=24,1,35,5,5
        S=e+ell+p
        t=F(S,3)
        self.assertEqual(t,20)
        self.assertLess(ell,t*F(1,10))
        self.assertLess(b+c,t*F(3,5))
        self.assertGreater(min(b,c),t*F(1,10))
        self.assertGreater(S-b-c,max(e,ell,p,b,c))
        u=S-t/2-e
        self.assertEqual(u,26)
        self.assertLess(u,p)
        self.assertGreater(u,ell)

    def test_existing_prime_aggregate_benchmark_is_not_per_block(self):
        eta=F(6,5)
        dp=((eta-1)/2,2-eta,1-eta/2,F(7,2)-2*eta)
        self.assertEqual(dp,(F(1,10),F(4,5),F(2,5),F(11,10)))
        self.assertEqual(max(dp),F(11,10))
        # A bound for a signed sum does not control arbitrary subblocks.
        blocks=(F(100),F(-99))
        self.assertLess(abs(sum(blocks)),max(map(abs,blocks)))


if __name__ == '__main__':
    unittest.main()
