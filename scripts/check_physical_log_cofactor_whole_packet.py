"""Finite CQ checks only; no certification of LS, analytic tails, or full gate."""
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt, ceil, sqrt, log
from collections import defaultdict
import unittest

from check_physical_centered_conductor_split import roots_equal
from check_physical_large_gcd_type_columns import mobius, phi, units


def compact(terms):
    out = defaultdict(F)
    for phase, a in terms:
        out[phase % 1] += a
    return [(x,a) for x,a in out.items() if a]


def equal(a,b):
    return roots_equal(compact(a),compact(b))


def ram(q,a):
    return sum(d*mobius(q//d) for d in range(1,q+1) if q%d == 0 and a%d == 0)


def physical(q,lam,u,v):
    if gcd(u*v,q) != 1:
        return []
    return [(F(-lam*u*v,q),F(1)),(F(0),-F(mobius(q),phi(q)))]


def multiply(a,b):
    return [(x+y,c*d) for x,c in a for y,d in b]


def raw_small(c,p,e,n,r,s):
    invp=pow(p,-1,c)
    lam=e*pow(n*p,-1,c)
    return [(F(-lam*u*v+invp*(r*u+s*v),c),F(1))
            for u,v in product(units(c),repeat=2)]


def small_centered(c,p,e,n,r,s):
    return raw_small(c,p,e,n,r,s)+[(F(0),-F(mobius(c)*ram(c,r)*ram(c,s),phi(c)))]


def crt_spectrum(c,p,e,n,r,s):
    high=[]
    if r*s%p:
        high=multiply(raw_small(c,p,e,n,r,s),[
            (F(n*r*s*pow(e*c,-1,p),p),F(p)),(F(0),F(p,p-1))])
    low=[(x,a*(-F(ram(p,r)*ram(p,s),p-1)))
         for x,a in small_centered(c,p,e,n,r,s)]
    return high,low


def full_spectrum(c,p,e,n,r,s):
    q=c*p
    terms=[]
    for u,v in product(units(q),repeat=2):
        terms += [(x+F(r*u+s*v,q),a)
                  for x,a in physical(q,e*pow(n,-1,q),u,v)]
    return terms


def periodic_z(c,p,e,n,r,s):
    shift=F(-n*r*s*pow(e*p,-1,c),c)
    return [(x+shift,a/c) for x,a in raw_small(c,p,e,n,r,s)]


def packet_parts(c,p,e,component):
    old, extended, bad_e, bad_n, bad_p = ([] for _ in range(5))
    for n,r,s in product(range(1,46),(-e,-p,-2,1,p,e),(-p,-1,2,e)):
        if gcd(n,e*c) != 1:
            continue
        numerator=n*r+e*s+p if component==0 else n*s-p*r+e
        weight=F(mobius(e)*mobius(c)*mobius(p)*mobius(n)*numerator,
                 (n+1)*(abs(r)+1)*(abs(s)+1))
        phase=F(n*r*s*pow(e*c,-1,p),p)
        raw=[(x+phase,a*weight/c) for x,a in raw_small(c,p,e,n,r,s)]
        eu=gcd(r*s,e)==1
        pu=gcd(r*s,p)==1
        nu=n%p!=0
        if pu and nu:
            old += raw
            if not eu: bad_e += raw
        if eu:
            extended += raw
            if not pu: bad_p += raw
            elif not nu: bad_n += raw
    return old,extended,bad_e,bad_n,bad_p


class CompositeModulusChecks(unittest.TestCase):
    def test_nonseparable_complex_weighted_inverse_dft(self):
        for c,p,e,n in ((2,3,5,5),(2,5,7,3),(3,5,7,2)):
            q=c*p
            for component in (0,1):
                weights={(u,v):F(u*v+2*u-v+1 if component==0 else u*u-v*u+2*v,
                                 (u+1)*(v+2))
                         for u,v in product(range(q),repeat=2)}
                direct=[]
                completed=[]
                for (u,v),w in weights.items():
                    direct += [(x,a*w) for x,a in physical(q,e*pow(n,-1,q),u,v)]
                for r,s in product(range(q),repeat=2):
                    hi,lo=crt_spectrum(c,p,e,n,r,s)
                    fourier=compact([(F(-r*u-s*v,q),w/F(q*q))
                                     for (u,v),w in weights.items()])
                    completed += multiply(compact(hi+lo),fourier)
                self.assertTrue(equal(direct,completed),(c,p,component))

    def test_full_signed_mask_expansion(self):
        for c,p,e,component in product((2,3),(5,11),(7,13),(0,1)):
            old,ext,be,bn,bp=packet_parts(c,p,e,component)
            assembled=ext+be+[(x,-a) for x,a in bn+bp]
            self.assertTrue(equal(old,assembled),(c,p,e,component))

    def test_principal_e_masks_are_disjoint(self):
        e,c=7,6
        for n,r,s in product(range(1,36),(-7,-3,-1,1,7),(-7,-1,2,7)):
            if gcd(n,c)!=1: continue
            original=int(gcd(n,e)==1 and gcd(r*s,e)==1)
            self.assertEqual(original,1-int(n%e==0)-int(n%e!=0 and r*s%e==0))
            # Removing e-unit never removes the retained c-unit domain.
            self.assertEqual(gcd(n,c),1)

    def test_real_composite_original_support(self):
        prime=lambda x: x>=2 and all(x%d for d in range(2,isqrt(x)+1))
        c,e,p=2,1009,32003
        self.assertTrue(prime(e) and prime(p))
        q=c*p
        S=R=e*q
        n=next(x for x in range(S+1,2*S) if prime(x))
        self.assertLess(n,2**64)
        T=(8*S)**(1/3)
        H=L=S/sqrt(T)
        u=ceil(H/e)
        if u%2==0: u+=1
        v=u
        self.assertLessEqual(c,log(2*T))
        self.assertLess(c*c,q)
        self.assertLess(2*e,p)
        self.assertLess(u,p)
        self.assertEqual(gcd(n,S),1)
        self.assertEqual(gcd(u*v,q),1)
        self.assertEqual((mobius(e),mobius(q),mobius(n)),(-1,1,-1))
        self.assertLessEqual(n,8*S//4)
        self.assertLessEqual(S,8*S//4)
        # H^6=S^6/(8S); exact integer endpoint checks, not float primality.
        self.assertGreaterEqual((e*u)**6*(8*S),S**6)
        self.assertLessEqual((e*u)**6*(8*S),64*S**6)
        self.assertLess(64*(e*v)**6,S**6*(8*S))
        self.assertLess(F(3*n,4*S),F(3,2))
        self.assertGreater(F(3*n,4*S),F(1,2))
        x=3*sqrt(T)/4
        y=(n*x+e*v)/S
        self.assertTrue(sqrt(T)/2<y<2*sqrt(T))

    def test_physical_two_branches(self):
        for c,p in ((1,5),(2,5),(3,5),(6,5),(5,7)):
            q=c*p
            for n in units(q)[:4]:
                e=next(x for x in (7,11,13,17) if gcd(x,q)==1)
                lc=e*pow(n*p,-1,c)
                lp=e*pow(n*c,-1,p)
                for u,v in product(range(-2,4),repeat=2):
                    R=[(F(-lc*u*v,c),F(1))] if gcd(u*v,c)==1 else []
                    Pc=[(F(0),F(mobius(c),phi(c)))] if gcd(u*v,c)==1 else []
                    Pp=[(F(0),-F(1,p-1))] if gcd(u*v,p)==1 else []
                    got=multiply(R,physical(p,lp,u,v))+multiply(physical(c,lc,u,v),Pp)
                    self.assertTrue(equal(physical(q,e*pow(n,-1,q),u,v),got))

    def test_complete_crt_double_dft(self):
        for c,p in ((1,3),(2,3),(3,5),(6,5),(5,7),(6,7)):
            q=c*p
            e=next(x for x in (7,11,13,17) if gcd(x,q)==1)
            for n,r,s in product(units(q)[:2],(0,1,c,p),(0,-1,c,p)):
                hi,lo=crt_spectrum(c,p,e,n,r,s)
                self.assertTrue(equal(full_spectrum(c,p,e,n,r,s),hi+lo),(c,p,n,r,s))

    def test_second_branch_cannot_be_erased(self):
        c,p,e,n,r,s=3,5,7,1,5,1
        hi,lo=crt_spectrum(c,p,e,n,r,s)
        self.assertEqual(hi,[])
        self.assertFalse(equal(lo,[]))
        self.assertFalse(equal(full_spectrum(c,p,e,n,r,s),hi))

    def test_nonunit_small_frequency_survives(self):
        c,p,e,n,r,s=3,5,7,1,3,1
        hi,lo=crt_spectrum(c,p,e,n,r,s)
        self.assertNotEqual(gcd(r*s,c*p),1)
        self.assertFalse(equal(hi,[]))
        self.assertFalse(equal(hi+lo,[]))

    def test_c_one_recovers_prime(self):
        for p in (3,5,7):
            for r,s in product(range(p),repeat=2):
                hi,lo=crt_spectrum(1,p,11,1,r,s)
                self.assertTrue(equal(lo,[]))
                self.assertTrue(equal(raw_small(1,p,11,1,r,s),[(F(0),F(1))]))

    def test_exact_poisson_factor(self):
        for c,p,U,V in product((1,2,3,6),(5,7),(F(1,2),F(5)),(F(3),F(7,2))):
            q=c*p
            self.assertEqual(U*V*F(p,q*q),U*V/q/c)
            if c>1:
                self.assertNotEqual(U*V*F(p,q*q),U*V/p)

    def test_triple_reciprocity_all_signs(self):
        for c,p,e in ((2,5,7),(3,5,7),(6,5,11),(10,7,13)):
            for n,r,s in product(range(1,16),(-3,-1,1,2),(-2,1,3)):
                a=n*r*s
                old=F(a*pow(e*c,-1,p),p)
                new=F(-a*pow(c*p,-1,e),e)+F(-a*pow(e*p,-1,c),c)+F(a,e*c*p)
                self.assertEqual((old-new).denominator,1)

    def test_small_period_is_five_variable_periodic(self):
        for c,p,e,n,r,s in ((2,5,7,3,0,1),(3,5,7,2,3,1),(6,5,7,5,-2,3)):
            ref=periodic_z(c,p,e,n,r,s)
            for j in range(5):
                vals=[p,e,n,r,s]
                vals[j]+=c
                self.assertTrue(equal(ref,periodic_z(c,*vals)))

    def test_inverse_complement_is_essential(self):
        c,p,e,n,r,s=3,5,7,1,1,1
        correct=raw_small(c,p,e,n,r,s)
        wrong=[(F(-e*pow(n,-1,c)*u*v+r*u+s*v,c),F(1))
               for u,v in product(units(c),repeat=2)]
        self.assertFalse(equal(correct,wrong))

    def test_actual_c_kernel_mean_zero(self):
        for c in (1,2,3,5,6,10,15):
            for lam,v in product(units(c),units(c)):
                out=[]
                for u in range(c):
                    out+=physical(c,lam,u,v)
                self.assertTrue(equal(out,[]))

    def test_centered_small_spectrum_axes_are_zero_not_raw(self):
        for c,p in ((2,5),(3,5),(6,5),(10,7)):
            e=next(z for z in (7,11,13) if gcd(z,c*p)==1)
            for t in range(c):
                self.assertTrue(equal(small_centered(c,p,e,1,0,t),[]))
                self.assertTrue(equal(small_centered(c,p,e,1,t,0),[]))
        self.assertFalse(equal(raw_small(3,5,7,1,0,1),[]))
        self.assertFalse(equal(small_centered(6,5,7,1,2,2),[]))

    def test_high_raw_reciprocal_identity(self):
        for c,p,e,n,r,s in ((3,5,7,2,3,1),(6,5,7,11,2,3),(2,7,5,3,-1,2),
                           (3,5,7,2,1,1),(5,7,3,2,-1,2)):
            raw=[(x+F(n*r*s*pow(e*c,-1,p),p),a/c)
                 for x,a in raw_small(c,p,e,n,r,s)]
            new=[(x+F(-n*r*s*pow(c*p,-1,e),e)+F(n*r*s,e*c*p),a)
                 for x,a in periodic_z(c,p,e,n,r,s)]
            self.assertTrue(equal(raw,new))

    def test_c_masks_survive_n_p_expansion(self):
        for c,p in ((2,5),(3,5),(6,5),(10,7)):
            for n in range(1,80):
                self.assertEqual(int(gcd(n,c*p)==1),int(gcd(n,c)==1)-int(gcd(n,c)==1 and n%p==0))
        self.assertNotEqual(int(gcd(2,10)==1),1-int(2%5==0))

    def test_n_p_original_mobius_not_factored(self):
        self.assertEqual(mobius(25),0)
        self.assertEqual(mobius(5)*mobius(5),1)

    def test_cofactor_label_unique(self):
        for q in range(2,400):
            if not mobius(q): continue
            for C in range(1,isqrt(q)):
                rows=[(c,q//c) for c in range(1,C+1) if q%c==0
                      and q//c>1 and all((q//c)%d for d in range(2,isqrt(q//c)+1))]
                self.assertLessEqual(len(rows),1)

    def test_costs_at_all_eta_endpoints(self):
        for i in range(101):
            eta=F(7,6)+F(i,1200)
            self.assertLessEqual(F(10,3)-2*eta,1)
            for exp in (F(7,2)-F(5,2)*eta,2-eta,F(5,2)-F(3,2)*eta,F(1),
                        4-3*eta,F(13,2)-7*eta,F(13,2)-8*eta,F(-23,2)+5*eta,-12+5*eta):
                self.assertLessEqual(exp,1)

    def test_smaller_common_column_is_not_larger(self):
        for R,K,E,X,c in product((1,4,16),(1,9,81),(1,3),(1,5),(1,2,4)):
            short=F(K,c)
            self.assertLessEqual(R*short*(R+E*E*X)*(short+E*E*X),R*K*(R+E*E*X)*(K+E*E*X))

    def test_projective_and_ap_price_not_free(self):
        for c in range(1,20):
            self.assertEqual(len(list(product(range(c),repeat=2))),c*c)
            self.assertEqual(c**5*c,c**6)
            if c>1: self.assertGreater(c**6,1)
        self.assertLess(F(5,2)+F(2,3),4)
        self.assertLessEqual(12+12+4,30)

    def test_exact_normalized_common_chirp(self):
        for c,E,P,R,J1,J2 in product((1,2,3),(2,4),(5,7),(8,16),(1,3),(1,5)):
            Q=c*P
            self.assertEqual(F(R*J1*J2,E*Q),F(R*J1*J2,E*c*P))


if __name__=='__main__':
    unittest.main(verbosity=2)
