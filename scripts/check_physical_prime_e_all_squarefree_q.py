"""AQ finite checks only. Does not certify hybrid LS, tails, or full gate."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt, ceil, sqrt
import unittest

from check_physical_three_mask_cofactor import (
    mobius, phi, units, prime_factors, primitive, gauss, assignments,
    spectral, reassembled_mu_kernel, equal, multiply, periodic_z, divs,
)
from check_physical_log_cofactor_whole_packet import raw_small, ram, physical


def centered(q,e,n,r,s):
    return raw_small(q,1,e,n,r,s)+[(F(0),-F(mobius(q)*ram(q,r)*ram(q,s),phi(q)))]


def raw_reciprocal(q,e,n,r,s):
    shift=F(-n*r*s*pow(q,-1,e),e)+F(n*r*s,e*q)
    return [(x+shift,b) for x,b in periodic_z(q,1,e,n,r,s)]


def principal_e_masks(e,n,r,s):
    # First add n=e*m while labels are unit, then add nonunit labels.
    return 1-int(n%e==0 and r*s%e!=0)-int(r*s%e==0)


def principal_common_coefficient(w,g):
    total=F(0)
    for e in prime_factors(w):
        z=w//e
        if gcd(e,g*z)>1 or gcd(z,g)>1: continue
        weight=F(1)
        for p in prime_factors(z): weight*=1-F(1,p*(p-1))
        total+=F(mobius(e)*mobius(z),phi(e))*weight
    return total


def natural_costs(eta,b):
    return (F(7,2)-F(5,2)*eta-F(5,2)*b,
            2-eta-b,
            F(5,2)-F(3,2)*eta-F(3,2)*b,
            F(1),
            F(10,3)-2*eta-F(13,6)*b,
            F(7,3)-2*eta-F(2,3)*b,
            F(7,3)-2*eta-F(7,6)*b,
            F(4,3)-2*eta+b/3,
            eta-2,F(13,2)-7*eta,4-3*eta,F(13,2)-8*eta)


class AllQChecks(unittest.TestCase):
    def test_centered_zero_axes_before_split(self):
        for q in (1,2,3,5,6,10,15,21,30,35):
            e=next(p for p in (5,7,11,13) if q%p)
            for n in units(q)[:3]:
                for s in (0,1,2,-3,q,2*q):
                    for r,t in ((0,s),(s,0),(q,s),(s,2*q)):
                        self.assertTrue(equal(centered(q,e,n,r,t),[]),(q,e,n,r,t))
                    axis=raw_small(q,1,e,n,0,s)
                    self.assertTrue(equal(axis,[(F(0),F(mobius(q)*ram(q,s)))]))
        self.assertFalse(equal(raw_small(15,1,7,1,0,1),[]))

    def test_nonseparable_weighted_full_inverse_dft(self):
        for q,e,n in ((2,3,1),(3,5,2),(6,5,5),(10,3,7)):
            for comp in (0,1):
                weights={(u,v):F(u*v+2*u-v+1 if comp==0 else u*u+v-2*u*v,
                                  (u+1)*(v+2)) for u,v in product(range(q),repeat=2)}
                original=[]; restored=[]
                for (u,v),w in weights.items():
                    original += [(x,a*w) for x,a in physical(q,e*pow(n,-1,q),u,v)]
                for r,s in product(range(1,q),repeat=2):
                    ft=[(F(-r*u-s*v,q),w/F(q*q)) for (u,v),w in weights.items()]
                    restored+=multiply(centered(q,e,n,r,s),ft)
                self.assertTrue(equal(original,restored),(q,comp))

    def test_allq_reciprocity_without_large_prime(self):
        for q,e in ((6,5),(10,3),(15,2),(21,5),(30,7),(35,3)):
            for n in units(q):
                for r,s in product((-q,-2,1,2,q),(-q,-1,2,q)):
                    original=[(x,a/F(q)) for x,a in raw_small(q,1,e,n,r,s)]
                    self.assertTrue(equal(original,raw_reciprocal(q,e,n,r,s)))

    def test_nonunit_labels_remain(self):
        q,e,n,r,s=6,5,1,2,3
        self.assertGreater(gcd(r*s,q),1)
        self.assertFalse(equal(raw_small(q,1,e,n,r,s),[]))
        self.assertTrue(equal(periodic_z(q,1,e,n,r,s),spectral(q,1,e,n,r,s)))

    def test_fullq_three_mask_original_signed_coefficients(self):
        for q,e in ((1,3),(2,3),(6,5),(10,3),(15,2),(21,5),(30,7),(35,3)):
            for n,r,s in product((1,2,3,5,6,7,9,10),(-3,0,1,2),(0,1,2,5)):
                weight=F(n*r-e*s+q,(n+1)*(abs(r)+1)*(abs(s)+1))
                old=[] if gcd(n,q)>1 else [(x,b*weight*mobius(e)*mobius(q)*mobius(n)) for x,b in periodic_z(q,1,e,n,r,s)]
                new=[(x,b*weight) for x,b in reassembled_mu_kernel(q,1,e,n,r,s)]
                self.assertTrue(equal(old,new),(q,e,n,r,s))

    def test_principal_expansion_disjoint_masks(self):
        for e,n,r,s in product((2,3,5,7),range(1,19),(-5,-3,1,3,5),(-7,-2,1,7)):
            self.assertEqual(principal_e_masks(e,n,r,s),int(gcd(n*r*s,e)==1))
        self.assertEqual(principal_e_masks(3,3,3,1),0)

    def test_ramanujan_nonzero_divisor_majorant(self):
        for q in range(1,61):
            for r in range(-80,81):
                if not r: continue
                self.assertLessEqual(abs(ram(q,r)),sum(d for d in divs(q) if r%d==0))
        # Finite counts have D/d, not D/d+1, when the zero point is absent.
        for q in (1,6,10,15,21,30,35,42):
            for D in (F(1,4),F(1,2),1,2,5,13,45):
                count=sum(abs(ram(q,r)) for r in range(-int(D),int(D)+1) if r)
                self.assertLessEqual(count,2*D*len(divs(q)))

    def test_ramanujan_short_scale_series_majorant(self):
        for D,d in product((F(1,4),F(1,2),1,3,10), (1,2,5,13,30)):
            y=F(D,d)
            finite=2*sum((1+F(j)/y)**-6 for j in range(1,60))
            self.assertLessEqual(finite,2*y)
            if y<1:
                self.assertLessEqual(y**6,y)

    def test_fused_modulus_has_duplicates_but_divisor_bound(self):
        rows=defaultdict(list)
        for e in (2,3,5,7,11,13,17,19):
            for lam in range(1,43):
                if mobius(lam) and gcd(e,lam)==1:
                    rows[e*lam].append((e,lam))
        self.assertGreater(len(rows[105]),1)
        for v,pairs in rows.items():
            self.assertLessEqual(len(pairs),len(divs(v)))
            self.assertEqual(len(set(e for e,lam in pairs)),len(pairs))
        self.assertIn((3,35),rows[105])
        self.assertIn((7,15),rows[105])

    def test_gauss_fusion_e_smaller_than_lambda(self):
        for e,lam in ((3,5),(3,35),(5,21),(7,15)):
            for psi,chi in product(primitive(e),primitive(lam)):
                lhs=[(x-psi[lam%e]-chi[e%lam],a)
                     for x,a in multiply(gauss(e,psi),gauss(lam,chi))]
                joint={n:psi[n%e]+chi[n%lam] for n in units(e*lam)}
                self.assertTrue(equal(lhs,gauss(e*lam,joint)))

    def test_principal_internal_product_masks(self):
        for g,lam in product((1,2,3,5,6,10), (1,3,5,7,15)):
            if gcd(g,lam)>1: continue
            direct=defaultdict(F)
            for e in (2,3,5,7,11,13):
                for z in range(1,31):
                    if not mobius(z) or gcd(e,lam*g*z)>1 or gcd(z,lam*g)>1: continue
                    weight=F(1)
                    for p in prime_factors(z): weight*=1-F(1,p*(p-1))
                    direct[e*z]+=F(mobius(e)*mobius(z),phi(e))*weight
            # Check a common product coefficient computed before the lambda mask.
            common=defaultdict(F)
            for e in (2,3,5,7,11,13):
                for z in range(1,31):
                    if not mobius(z) or gcd(e,g*z)>1 or gcd(z,g)>1: continue
                    weight=F(1)
                    for p in prime_factors(z): weight*=1-F(1,p*(p-1))
                    common[e*z]+=F(mobius(e)*mobius(z),phi(e))*weight
            common={w:a for w,a in common.items() if gcd(w,lam)==1 and a}
            self.assertEqual({w:a for w,a in direct.items() if a},common)
        self.assertEqual(principal_common_coefficient(9,1),0)  # e=z=3 forbidden.
        self.assertEqual(principal_common_coefficient(15,3),0)  # e-g OR z-g forbidden.

    def test_fused_character_e_mask_zero_extension(self):
        for e,lam,g in ((3,5,2),(5,3,7),(7,15,2)):
            for z in range(1,22):
                physical_unit=gcd(e,lam*g*z)==1 and gcd(z,lam*g)==1
                separated=(gcd(e,g)==1 and gcd(lam,g)==1 and gcd(z,g)==1
                           and gcd(z,e*lam)==1)
                self.assertEqual(physical_unit,separated)

    def test_normalizations_with_all_original_rows(self):
        for T,E,Q,R,U,V in ((7,5,11,101,3,4),(13,17,19,1009,7,11)):
            S=E*Q; D1=F(Q,U); D2=F(Q,V)
            rows=E*Q*R
            correction=F(T,R*S)*rows*F(U*V,Q*Q)*F(1,Q)*D1*D2
            self.assertEqual(correction,F(T,Q))
            raw=F(T,R*S)*rows*F(U*V,Q)*D1*D2
            self.assertEqual(raw,T*Q)

    def test_full_conductor_exponent_range(self):
        for i,j in product(range(31),range(41)):
            eta=F(7,6)+F(i,360)
            b=(3-eta)*F(j,40)
            self.assertTrue(all(v<=1 for v in natural_costs(eta,b)),(eta,b,natural_costs(eta,b)))
        self.assertEqual(natural_costs(F(6,5),0)[3],1)
        self.assertEqual(natural_costs(F(7,6),0)[4],1)
        self.assertGreater(natural_costs(F(23,20),0)[4],1)

    def test_new_balanced_semiprime_q_original_support(self):
        prime=lambda n: n>=2 and all(n%d for d in range(2,isqrt(n)+1))
        e,p1,p2=1009,167,173
        self.assertTrue(all(prime(p) for p in (e,p1,p2)))
        q=p1*p2; S=R=e*q; N=8*S; T=N**(1/3)
        E=900; Q=28000
        self.assertTrue(E<=e<2*E and Q<=q<2*Q)
        self.assertTrue(p1**7>N and p2**7>N)  # each complement >T^(3/7).
        self.assertEqual(mobius(q),1)
        self.assertTrue(E**5<N*N<(4*E)**5)
        H=L=S/sqrt(T)
        u=ceil(H/e)
        while gcd(u,q)>1: u+=1
        n=next(t for t in range(S+1,2*S) if prime(t))
        self.assertLess(n,2**64)
        self.assertEqual(gcd(n,e*q),1)
        self.assertEqual(gcd(u*u,q),1)
        self.assertTrue(H<=e*u<=2*H)
        self.assertLessEqual(n,N//4)
        self.assertLessEqual(S,N//4)
        x=3*sqrt(T)/4; y=(n*x+e*u)/S
        self.assertTrue(sqrt(T)/2<y<2*sqrt(T))


if __name__=='__main__': unittest.main(verbosity=2)
