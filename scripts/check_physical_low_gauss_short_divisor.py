#!/usr/bin/env python3
"""Finite GW guards; no test certifies hybrid Weyl, tails, or the full gate."""
from fractions import Fraction as F
from itertools import product
from math import gcd, ceil, isqrt, sqrt
import unittest

from check_physical_centered_conductor_split import characters, roots_equal
from check_physical_large_gcd_type_columns import mobius, phi, units
from check_physical_squarefree_type_descent import divisors


def n_ie(n, a, d):
    if gcd(n,d)!=1:
        return 0
    return sum(mobius(f)*mobius(f*(n//f)) for f in divisors(gcd(n,a)))


def label_ie(d, rho, sigma):
    rows=[]
    for j in divisors(d):
        k=d//j
        if rho%j or sigma%k: continue
        r=rho//j; s=sigma//k
        for v in divisors(gcd(r,k)):
            rows.append((j,k,v,r//v,s,mobius(v)))
    return rows


def shell(E, n):
    return ceil(E)<=n<=ceil(2*E)-1


def exponents(eta, z, gamma):
    return (F(10,3)-2*eta+gamma/2,
            F(7,3)-2*eta+4*z/3+gamma,
            F(7,3)-2*eta+5*z/6+gamma/2,
            F(4,3)-2*eta+7*z/3+gamma)


def rebuilt(e,q,n,rho,sigma,Z,D):
    out=[]
    for ell in divisors(e):
        if ell>=max(2,Z): continue
        for d in divisors(e//ell):
            if d>D or gcd(n,d)!=1: continue
            a=e//(ell*d)
            for f in divisors(gcd(n,a)):
                m=n//f; b=a//f
                for j,k,v,z,s,mu_v in label_ie(d,rho,sigma):
                    for cond,chi in characters(ell):
                        if cond!=ell or gcd(m*b*z*s,ell)!=1: continue
                        coeff=F(mobius(ell)*mobius(d)*d*mobius(f)*mobius(f*m)*mu_v,phi(e))
                        for y in units(ell):
                            phase=F(y,ell)-chi[y]-chi[b%ell]+chi[(-m)%ell]-chi[q%ell]+chi[v%ell]+chi[z%ell]+chi[s%ell]
                            out.append((phase,coeff))
    return out


class LowGauss(unittest.TestCase):
    def test_complex_weighted_full_reassembly(self):
        for e,q,Z,D in ((15,37,4,2),(30,67,6,3),(35,73,8,5),(42,89,8,7)):
            left=[]; right=[]
            for n,r,s in product(range(1,9),(-3,-1,2,3),(-2,1,3)):
                weight=F(mobius(q)*(n+e*r-q*s),q*(n+1)*(abs(r)+1)*(abs(s)+1))
                phase=F((n+e+r*s)%4,4)
                right.extend((phase+p,weight*w) for p,w in rebuilt(e,q,n,r,s,Z,D))
                if gcd(n,e)!=1: continue
                for ell in divisors(e):
                    if ell>=max(2,Z): continue
                    c=e//ell
                    dd=sum(mobius(d)*d for d in divisors(gcd(c,r*s)) if d<=D)
                    for cond,chi in characters(ell):
                        if cond!=ell or gcd(r*s,ell)!=1: continue
                        for y in units(ell):
                            p=F(y,ell)-chi[y]-chi[c%ell]+chi[(r*s)%ell]+chi[(-n)%ell]-chi[q%ell]
                            left.append((phase+p,weight*F(mobius(ell)*mobius(n)*dd,phi(e))))
            self.assertTrue(roots_equal(left,right),(e,Z,D))

    def test_n_mask_and_original_mobius(self):
        for a,d,n in product((1,2,3,5,6,7,10,15), (1,2,3,5,6),range(1,31)):
            if not mobius(a*d): continue
            want=mobius(n) if gcd(n,a*d)==1 else 0
            self.assertEqual(n_ie(n,a,d),want,(n,a,d))

    def test_label_allocation_then_unit_ie(self):
        for d,r,s in product((1,2,3,6,10,15),range(-6,7),range(-6,7)):
            if not r or not s: continue
            total=sum(weight for j,k,v,z,t,weight in label_ie(d,r,s))
            self.assertEqual(total,int(r*s%d==0),(d,r,s))

    def test_integer_shell_fractional_endpoints(self):
        for E in (F(1),F(3,2),F(11,3),F(7)-F(1,1000),F(7)+F(1,1000)):
            for n in range(1,20):
                self.assertEqual(shell(E,n),E<=n<2*E,(E,n))

    def test_physical_four_costs(self):
        self.assertEqual(exponents(F(6,5),F(1,5),F(2,15)),
                         (F(1),F(1,3),F(1,6),F(-7,15)))

    def test_mu_fm_is_not_a_free_product(self):
        self.assertEqual(n_ie(4,2,1),0)
        wrong=sum(mobius(f)*mobius(f)*mobius(4//f) for f in (1,2))
        self.assertEqual(wrong,-1)

    def test_no_extra_m_b_unit_mask(self):
        good=sum(mobius(f)*mobius(2) for f in (1,2))
        wrong=sum(mobius(f)*mobius(2) for f in (1,2) if gcd(2//f,2//f)==1)
        self.assertEqual(good,0)
        self.assertEqual(wrong,1)

    def test_label_ie_needs_canceling_noncanonical_rows(self):
        rows=label_ie(6,2,6)
        self.assertIn((1,6,1,2,1,1),rows)
        self.assertIn((1,6,2,1,1,-1),rows)
        self.assertIn((2,3,1,1,2,1),rows)
        self.assertEqual(sum(row[-1] for row in rows),1)

    def test_short_divisor_is_not_gcd_projection(self):
        # e=15, principal, rho sigma=3: short d=1 term is nonzero,
        # even though gcd(e,rho sigma)>D=1.
        partial=F(sum(mobius(d)*d for d in divisors(3) if d<=1),phi(15))
        complete=F(sum(mobius(d)*d for d in divisors(3)),phi(15))
        self.assertEqual(partial,F(1,8))
        self.assertEqual(complete,F(-1,4))
        self.assertEqual(gcd(15,3)>1,True)

    def test_exact_chirp_after_all_three_substitutions(self):
        for ell,d,f,b,q in ((3,10,7,11,1009),(1,6,5,7,1009),(5,6,7,11,1009)):
            e=ell*d*f*b
            for j in divisors(d):
                k=d//j
                for v in divisors(k):
                    for m,z,s in ((1,2,-3),(3,-2,-1),(7,1,2)):
                        n=f*m; rho=j*v*z; sigma=k*s
                        self.assertEqual(F(n*rho*sigma,e*q),F(m*v*z*s,ell*b*q))

    def test_original_phi_normalization(self):
        for ell,d,f,b in ((3,10,7,11),(1,6,5,7),(5,6,7,11)):
            e=ell*d*f*b
            self.assertEqual(phi(e),phi(ell)*phi(d)*phi(f)*phi(b))
            self.assertEqual(F(e,phi(e)),F(ell,phi(ell))*F(d,phi(d))*F(f,phi(f))*F(b,phi(b)))

    def test_four_cost_squared_identity(self):
        for R,S,l,x,d,f in product((2,5),(3,7),(1,2),(1,3),(1,6),(1,5)):
            L=l**3; X=x**3
            N1=F(R,f); N2=F(S,L*d*f)
            left=l**5*d*x**2*N1*N2*(N1+L*L*X)*(N2+L*L*X)
            right=(F(R*R*S*S*x*x,l*d*f**4)
                   +F(R*R*S*x**5*l**8,f**3)
                   +F(S*S*R*x**5*l**5,d*f**3)
                   +F(R*S*x**8*l**14,f*f))
            self.assertEqual(left,right)

    def test_primitive_f_character_cancels_only_on_units(self):
        for ell in (3,5,7,15):
            for cond,chi in characters(ell):
                if cond!=ell: continue
                for f,m,b in product(units(ell),units(ell),units(ell)):
                    self.assertEqual((chi[(f*m)%ell]-chi[(f*b)%ell]-chi[m]+chi[b])%1,0)

    def test_short_integer_support_and_unchanged_X(self):
        for J1,J2 in product((F(1,2),F(1),F(3),F(8)),repeat=2):
            for d in (1,2,3,6):
                for j in divisors(d):
                    k=d//j
                    for v in divisors(k):
                        zs=[z for z in range(1,20) if J1/2<=j*v*z<=2*J1]
                        ss=[s for s in range(1,20) if J2/2<=k*s<=2*J2]
                        if zs and ss:
                            self.assertGreaterEqual(J1/(j*v),F(1,2))
                            self.assertGreaterEqual(J2/k,F(1,2))
                            self.assertLessEqual(d*v,4*J1*J2)
                        self.assertEqual((J1/(j*v))*(J2/k)*d*v,J1*J2)

    def test_large_prime_f_or_b_disjoint_complete(self):
        counts=[0,0]
        for e in range(2,401):
            if not mobius(e): continue
            primes=[p for p in divisors(e) if len(divisors(p))==2 and p*p>2*e]
            if not primes: continue
            p=primes[0]; h=e//p
            for ell in divisors(h):
                for d in divisors(h//ell):
                    for f in divisors(e//(ell*d)):
                        b=e//(ell*d*f)
                        cases=(f%p==0,b%p==0)
                        self.assertEqual(sum(cases),1)
                        counts[cases[1]]+=1
                        cofactor=ell*d*(f//p)*b if cases[0] else ell*d*f*(b//p)
                        self.assertEqual(cofactor,h)
        self.assertGreater(min(counts),0)

    def test_long_d_forces_large_prime_in_actual_family(self):
        for e in range(2,401):
            if not mobius(e): continue
            ps=[p for p in divisors(e) if len(divisors(p))==2 and p*p>2*e]
            if not ps: continue
            p=ps[0]; h=e//p
            for ell in divisors(h):
                for d in divisors(e//ell):
                    self.assertEqual(d>h,p<=d and d%p==0)

    def test_small_cofactor_tail_and_no_full_sf_claim(self):
        eta=F(6,5); beta=F(2,15)
        tail=F(7,2)-eta+3*beta/2+6*(F(1,2)+beta-eta)
        self.assertEqual(tail,F(-9,10))
        self.assertGreater(eta-beta,eta/2)
        self.assertGreater(eta-beta,F(1,5))
        self.assertGreater(exponents(eta,F(1,5),F(1))[0],1)

    def test_family_witness_with_growing_cofactor_scales(self):
        # T~Y^10, h~Y, p~Y^11, q~Y^18. Checks scales, not primality density.
        t,e,h,p,q=F(10),F(12),F(1),F(11),F(18)
        self.assertEqual(e,h+p)
        self.assertEqual(3*t,e+q)
        self.assertEqual(e/t,F(6,5))
        self.assertLess(h/t,F(2,15))
        self.assertGreater(p,e/2)

    def test_original_integer_kernel_support(self):
        prime=lambda n:n>=2 and all(n%d for d in range(2,isqrt(n)+1))
        h,p,q=2,101,100003
        self.assertTrue(prime(p) and prime(q))
        e=h*p; S=e*q; T=(8*S)**(1/3); E=e
        n=next(n for n in range(S+1,2*S) if prime(n))
        H=S/sqrt(T); u=v=ceil(H/e); x=3*sqrt(T)/4
        y=(n*x+e*v)/S
        self.assertLessEqual(h,T**F(2,15))
        self.assertGreater(p,sqrt(2*E))
        self.assertGreater(p,T**F(1,5))
        self.assertEqual(gcd(n,e*q),1)
        self.assertEqual(gcd(u*v,q),1)
        self.assertTrue(H<=e*u<=2*H)
        self.assertTrue(sqrt(T)/2<=y<=2*sqrt(T))
        self.assertTrue(S<n<2*S)

    def test_sobolev_weight_and_hard_shell_modes_do_not_mix(self):
        dimension=6; label_weight=F(2,3)
        self.assertGreater(4,F(dimension,2)+label_weight)
        self.assertLessEqual(12+12+4,30)
        # If shell mode wrongly reaches both labels, weighted sum would
        # demand extra regularity; actual mode vector only ell/b nonzero.
        shell_mode=(0,7,0,7,0,0)
        self.assertEqual(shell_mode[4:],(0,0))


if __name__=='__main__':
    unittest.main()
