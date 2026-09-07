"""Exact TM candidate checks. No analytic LS/tail or coverage certification."""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import gcd, lcm, isqrt, ceil, sqrt
import unittest

from check_physical_centered_conductor_split import characters, prime_factors, roots_equal
from check_physical_large_gcd_type_columns import mobius, phi, units
from check_physical_log_cofactor_whole_packet import raw_small, periodic_z, compact, equal, multiply


@lru_cache(None)
def primitive(q):
    return [ch for ell,ch in characters(q) if ell==q]


def divs(q):
    return [d for d in range(1,q+1) if q%d==0]


def gauss(q,ch,conjugate=True):
    return [(F(a,q)+(-1 if conjugate else 1)*ch[a], F(1)) for a in units(q)]


def local_coeff(p):
    w=1-F(1,p*(p-1))
    alpha=F(p-2,p-1)
    beta=F(1,p-1)
    # bit 0 n; bit 1 rho; bit 2 sigma.
    return {0:w,1:-w,2:-alpha,4:-alpha,3:alpha,5:alpha,6:-beta,7:beta}


def local_A(p,r,s):
    R,S=int(r%p==0),int(s%p==0)
    return 1-F(1,p*(p-1))-F(p-2,p-1)*(R+S)-F(1,p-1)*R*S


def factor_weight(a,r,s):
    v=F(1)
    for p in prime_factors(a): v*=local_A(p,r,s)
    return v


def spectral(c,p,e,n,r,s,omit_a=False):
    if gcd(n,c)!=1: return []
    terms=[]
    for ell in divs(c):
        a=c//ell
        if gcd(n*r*s,ell)!=1: continue
        scalar=factor_weight(a,r,s)/F(ell*phi(ell))
        for ch in primitive(ell):
            arg=e*p*(1 if omit_a else a)
            phase=ch[(-n*r*s)%ell]-ch[arg%ell]
            terms += [(x+phase,v*scalar) for x,v in gauss(ell,ch)]
    return terms


def polynomial_mask(a,n,r,s):
    primes=prime_factors(a)
    total=F(0)
    for masks in product(range(8),repeat=len(primes)):
        coeff=F(1)
        for p,mask in zip(primes,masks):
            coeff*=local_coeff(p)[mask]
            if mask&1 and n%p: coeff=0
            if mask&2 and r%p: coeff=0
            if mask&4 and s%p: coeff=0
        total+=coeff
    return total


def assignments(g):
    ps=prime_factors(g)
    for masks in product(range(1,8),repeat=len(ps)):
        f=j=k=1
        v=F(1)
        for p,mask in zip(ps,masks):
            v*=local_coeff(p)[mask]
            if mask&1: f*=p
            if mask&2: j*=p
            if mask&4: k*=p
        yield f,j,k,v


def reassembled_mu_kernel(c,p,e,n,r,s):
    terms=[]
    for ell in divs(c):
        a=c//ell
        if gcd(n*r*s,ell)!=1: continue
        for g in divs(a):
            z=a//g
            w=F(1)
            for prime in prime_factors(z): w*=local_coeff(prime)[0]
            for f,j,k,v in assignments(g):
                if n%f or r%j or s%k: continue
                m,rr,ss=n//f,r//j,s//k
                coeff=mobius(e)*mobius(ell)*mobius(g)*mobius(z)*mobius(p)*mobius(f*m)*v*w/F(ell*phi(ell))
                for ch in primitive(ell):
                    # Cancel exactly g from both n*r*s and a=g*z.
                    phase=ch[(-(f*j*k//g)*m*rr*ss)%ell]-ch[(e*p*z)%ell]
                    terms += [(x+phase,b*coeff) for x,b in gauss(ell,ch)]
    return terms


class ThreeMaskChecks(unittest.TestCase):
    def test_prime_raw_all_unit_and_nonunit_labels(self):
        for ell in (2,3,5,7,11):
            p=next(x for x in (13,17,19) if x!=ell)
            e=23
            for n in units(ell):
                for r,s in product(range(ell),repeat=2):
                    U=int(r%ell!=0 and s%ell!=0)
                    B=int(r%ell==0 and s%ell==0)
                    rhs=[(F(0),F(U-B)),(F(-n*r*s*pow(e*p,-1,ell),ell),F(1,ell))]
                    self.assertTrue(equal(periodic_z(ell,p,e,n,r,s),rhs),(ell,n,r,s))

    def test_global_primitive_expansion_with_crt_complement(self):
        for c in (1,2,3,5,6,10,15,21,30):
            p,e=31,37
            for n in units(c)[:3]:
                for r,s in product((0,1,2,-3,c),(0,1,-2,c//2,c)):
                    self.assertTrue(equal(periodic_z(c,p,e,n,r,s),spectral(c,p,e,n,r,s)),(c,n,r,s))

    def test_crt_complement_omission_detected(self):
        c,p,e,n,r,s=15,31,37,1,1,1
        self.assertFalse(equal(spectral(c,p,e,n,r,s),spectral(c,p,e,n,r,s,True)))

    def test_two_has_no_primitive_character(self):
        self.assertEqual(primitive(2),[])
        self.assertEqual(len(primitive(1)),1)
        self.assertEqual(local_A(2,0,0),F(-1,2))
        self.assertEqual(local_A(2,1,0),F(1,2))

    def test_unit_extension_zero_without_inverse(self):
        for c in (2,6,15,30):
            for n in range(1,c+1):
                if gcd(n,c)>1:
                    self.assertEqual(spectral(c,31,37,n,1,1),[])

    def test_all_mobius_mask_reassembly_with_joint_signed_weight(self):
        for c in (1,2,3,6,10,15,30):
            p,e=31,37
            for n,r,s in product((1,2,3,5,7,9,10),(-2,0,1,3),(0,1,2,5)):
                weight=F(n*r+e*s-p,(n+1)*(abs(r)+1)*(abs(s)+1))
                old=[] if gcd(n,c)>1 else [(x,b*weight*mobius(e)*mobius(c)*mobius(p)*mobius(n)) for x,b in periodic_z(c,p,e,n,r,s)]
                new=[(x,b*weight) for x,b in reassembled_mu_kernel(c,p,e,n,r,s)]
                self.assertTrue(equal(old,new),(c,n,r,s))

    def test_exact_eight_term_polynomial(self):
        for p in (2,3,5,7,11):
            for N,R,S in product((0,1),repeat=3):
                n,r,s=(0 if flag else 1 for flag in (N,R,S))
                self.assertEqual(polynomial_mask(p,n,r,s),(1-N)*local_A(p,r,s))
        for a in (6,10,15,30):
            for n,r,s in product((0,1,2,3,5,6),repeat=3):
                self.assertEqual(polynomial_mask(a,n,r,s),int(gcd(n,a)==1)*factor_weight(a,r,s))

    def test_lcm_assignment_and_empty_complement(self):
        for a in (1,2,3,6,15,30):
            for n,r,s in product((1,2,3,5,6),repeat=3):
                reassembled=F(0)
                for g in divs(a):
                    z=a//g
                    w=F(1)
                    for p in prime_factors(z): w*=local_coeff(p)[0]
                    for f,j,k,v in assignments(g):
                        self.assertEqual(lcm(f,j,k),g)
                        self.assertEqual((f*j*k)%g,0)
                        if n%f==r%j==s%k==0: reassembled+=v*w
                self.assertEqual(reassembled,polynomial_mask(a,n,r,s))

    def test_original_mobius_not_refactored(self):
        self.assertEqual(mobius(2*2),0)
        self.assertEqual(mobius(2)*mobius(2),1)
        # Extra mu(f) flips a genuine nonempty assignment.
        f,j,k,v=next(row for row in assignments(3) if row[:3]==(3,1,1))
        self.assertNotEqual(v*mobius(f*2),v*mobius(f)*mobius(f*2))
        # A cancelled n-unit restriction is not restored termwise.
        self.assertNotEqual(polynomial_mask(3,3,1,1),local_coeff(3)[0])

    def test_joint_gauss_fusion(self):
        for e,ell in ((5,1),(7,3),(7,5),(11,15)):
            for psi,chi in product(primitive(e),primitive(ell)):
                lhs=multiply(gauss(e,psi),gauss(ell,chi))
                shift=-psi[ell%e]-chi[e%ell]
                lhs=[(x+shift,v) for x,v in lhs]
                joint={n:psi[n%e]+chi[n%ell] for n in units(e*ell)}
                self.assertTrue(equal(lhs,gauss(e*ell,joint)),(e,ell))

    def test_fused_character_argument_signs(self):
        e,ell,g,z,p,f,j,k=11,3,10,7,13,2,5,10
        kap=f*j*k//g
        for psi,chi in product(primitive(e),primitive(ell)):
            for m,r,s in ((1,1,1),(5,-1,2),(7,2,-1)):
                n,rho,sigma=f*m,j*r,k*s
                c=ell*g*z
                old=psi[-n*rho*sigma%e]-psi[c*p%e]+chi[-n*rho*sigma%ell]-chi[e*p*g*z%ell]
                new=psi[-kap*m*r*s%e]+chi[-kap*m*r*s%ell]-psi[z*p%e]-chi[z*p%ell]-psi[ell%e]-chi[e%ell]
                self.assertEqual((old-new).denominator,1)

    def test_original_continuous_chirp_exact(self):
        for g in (1,2,3,6,15):
            for f,j,k,v in assignments(g):
                for ell,z,p,e,m,r,s in ((7,11,13,17,19,2,-3),(1,5,7,11,3,-1,4)):
                    old=F(f*m*j*r*k*s,e*ell*g*z*p)
                    self.assertEqual(old,F((f*j*k//g)*m*r*s,e*ell*z*p))

    def test_all_dual_lengths_include_theta(self):
        for Q,D1,D2,J1,J2,L,g,j,k in product((12,30),(2,4),(3,6),(F(1,2),1,8),(1,12),(1,3),(1,5),(1,2),(1,3)):
            theta=F(J1,D1)*F(J2,D2)
            actual=F(Q*J1*J2,L*g*j*k)
            self.assertEqual(actual,F(Q*D1*D2,L*g*j*k)*theta)
            if theta!=1:
                self.assertNotEqual(actual,F(Q*D1*D2,L*g*j*k))

    def test_all_denominators_dominate_worst(self):
        for g in (1,2,3,5,6,10,15,30,42):
            for f,j,k,v in assignments(g):
                worst=f*g*j*k
                squares=((f*g*j*k)**2,f*f*g*j*k,g*g*j*j*k*k*f,
                         f*f*g*g*j*k,f*f*g*j*k,g*g*f*j*k)
                self.assertTrue(all(d>=worst for d in squares))
                self.assertLessEqual(abs(v),1)
        for p in (2,3,5,7):
            # Use squared denominators to verify subset multiplicities exactly.
            bysize=defaultdict(int)
            for f,j,k,_ in assignments(p):
                size=sum(int(x%p==0) for x in (f,j,k))
                bysize[size]+=1
                self.assertEqual(f*p*j*k,p**(1+size))
            self.assertEqual(dict(bysize),{1:3,2:3,3:1})

    def test_primitive_modulus_unique_large_prime(self):
        pairs={}
        for e in (11,13,17,19,23):
            for ell in range(1,11):
                if mobius(ell):
                    self.assertNotIn(e*ell,pairs)
                    pairs[e*ell]=(e,ell)

    def test_raw_zero_axis_cannot_be_deleted(self):
        for c in (2,3,5,6,10,15):
            p,e,n=31,37,1
            for s in range(c):
                full=[]
                nonzero=[]
                for r in range(c):
                    terms=raw_small(c,p,e,n,r,s)
                    full+=terms
                    if r: nonzero+=terms
                self.assertTrue(equal(full,[]))
                axis=raw_small(c,p,e,n,0,s)
                self.assertTrue(equal(nonzero,[(x,-a) for x,a in axis]))
        self.assertFalse(equal(raw_small(3,31,37,1,0,1),[]))
        self.assertFalse(equal(raw_small(1,31,37,1,0,1),[]))

    def test_exact_costs_full_region(self):
        for i,j in product(range(31),range(31)):
            eta=F(7,6)+F(i,360)
            gamma=F(j,70)
            costs=[F(7,2)-F(5,2)*eta,2-eta,F(5,2)-F(3,2)*eta,F(1),
                   F(10,3)-2*eta,F(7,3)-2*eta,F(7,3)-2*eta,
                   F(4,3)-2*eta+gamma/3,
                   -12+5*eta+7*gamma,F(-23,2)+5*eta+6*gamma,
                   1+gamma-F(1,2),1+7*gamma-3,
                   1+gamma+F(5,2)-6*eta,
                   1+7*gamma+F(5,2)-6*(3-eta)]
            self.assertTrue(all(x<=1 for x in costs),(eta,gamma,costs))
        self.assertGreater(1+7*F(1,2)-3,1)

    def test_original_polynomial_cofactor_support(self):
        prime=lambda n: n>=2 and all(n%d for d in range(2,isqrt(n)+1))
        c,e,p=11,1009,3203
        self.assertTrue(all(prime(x) for x in (c,e,p)))
        q=c*p
        S=R=e*q
        N=8*S
        T=N**(1/3)
        E=900
        Q=33000
        self.assertTrue(E<=e<2*E and Q<=q<2*Q)
        self.assertLess(c**7,N)  # c < T^(3/7), exact.
        self.assertLess(c*c,Q)
        self.assertLess(2*e,p)
        # Finite comparison constants for the eta=6/5 family.
        self.assertLess(E**5,N*N)
        self.assertGreater((4*E)**5,N*N)
        H=L=S/sqrt(T)
        u=ceil(H/e)
        while gcd(u,q)>1: u+=1
        v=u
        n=next(j for j in range(S+1,2*S) if prime(j))
        self.assertLess(n,2**64)
        self.assertEqual(gcd(n,S),1)
        self.assertEqual(gcd(u*v,q),1)
        self.assertLess(2*u,p)
        self.assertLessEqual(n,N//4)
        self.assertLessEqual(S,N//4)
        self.assertGreaterEqual((e*u)**6*N,S**6)
        self.assertLessEqual((e*u)**6*N,64*S**6)
        x=3*sqrt(T)/4
        y=(n*x+e*v)/S
        self.assertTrue(sqrt(T)/2<y<2*sqrt(T))


if __name__=='__main__': unittest.main(verbosity=2)
