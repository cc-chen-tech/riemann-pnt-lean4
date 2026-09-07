"""Exact finite guards for the common-gcd full h/delta adapter.

These checks do not prove the analytic large-sieve, exponent-pair or tail bounds.
Run with python -B scripts/check_physical_common_gcd_full_reassembly.py.
"""
from fractions import Fraction as F
from itertools import product
from math import gcd
from pathlib import Path
import unittest
from check_physical_large_gcd_type_columns import mobius, phi
from check_physical_squarefree_type_descent import divisors
from check_physical_full_delta_rough_moduli import ram, weight
from check_physical_centered_conductor_split import roots_equal

def vals(n,m,s,e):
    return range((1-n*m+e-1)//e,(3*s-n*m)//e+1)

def rawgrid(n,m,s,e,q):
    return sum((weight(n,m,s,n*m+e*v) for v in vals(n,m,s,e)
                if (n*m+e*v)%q==0),F(0))

def unitgrid(n,m,s,e,q):
    return sum((weight(n,m,s,n*m+e*v) for v in vals(n,m,s,e)
                if gcd(v,q)==1),F(0))

class CommonChecks(unittest.TestCase):
    def test_common_gcd_indicator_and_canonical(self):
        count=0
        for q,u,v in product((1,2,3,6,10,15,30,42),range(-10,11),range(-10,11)):
            self.assertEqual(int(gcd(q,gcd(u,v))==1),
                             sum(mobius(d) for d in divisors(gcd(q,gcd(u,v)))))
            if gcd(q,gcd(u,v))>1:
                continue
            a,b=gcd(q,u),gcd(q,v)
            self.assertEqual(gcd(a,b),1)
            l=q//(a*b)
            self.assertEqual(F(ram(q,u*v),phi(q)),F(mobius(l),phi(l)))
            count+=1
        print("canonical_exact",count)

    def test_full_h_raw_and_actual_principal_dft(self):
        count=0
        for q,e,n,v,m in product((1,2,3,5,6,10,15,30),(1,7),(1,11),range(-4,5),range(1,9)):
            if gcd(e*n,q)>1:
                continue
            g=gcd(q,v); l=q//g
            raw=[(-F(u*(m+e*v*pow(n,-1,q)),q),F(1))
                 for u in range(q) if gcd(u,g)==1]
            prin=[(-F(u*m,q),F(ram(q,u*v),phi(q)))
                  for u in range(q) if gcd(u,g)==1]
            expected_raw=l*ram(g,m)*int((n*m+e*v)%l==0)
            expected_prin=F(l*ram(g,m),phi(l))*int(gcd(m,l)==1)
            self.assertTrue(roots_equal(raw,[(F(0),F(expected_raw))]),(q,e,n,v,m))
            self.assertTrue(roots_equal(prin,[(F(0),expected_prin)]),(q,e,n,v,m))
            count+=1
        print("full_h_raw_principal_DFT",count)

    def test_full_raw_signed_mark_weighted_identity(self):
        count=0
        for s,E,n,m in product((6,10,30,42,70,105),(1,2,4,8),(1,11),(1,2,3)):
            if gcd(n,s)>1:
                continue
            direct=F(0)
            for e in divisors(s):
                q=s//e
                if not E<=e<2*E or q==1:
                    continue
                for v in vals(n,m,s,e):
                    g=gcd(q,v); l=q//g
                    kernel=l*ram(g,m)*int((n*m+e*v)%l==0)
                    direct+=mobius(e)*mobius(q)*mobius(n)*kernel*weight(n,m,s,n*m+e*v)
            grouped=F(0)
            for ep in divisors(s):
                qp=s//ep
                mark=sum(mobius(d) for d in divisors(ep) if E<=ep//d<2*E and d*qp>1)
                grouped+=mark*mobius(ep)*mobius(qp)*mobius(n)*qp*rawgrid(n,m,s,ep,qp)
            self.assertEqual(direct,grouped,(s,E,n,m))
            count+=1
        print("weighted_raw_signed_mark",count)

    def test_actual_principal_ramanujan_mark_weighted_identity(self):
        count=0
        for s,E,n,m in product((6,10,30,42,70,105),(1,2,4,8),(1,11),(1,2,3)):
            if gcd(n,s)>1:
                continue
            direct=F(0)
            for e in divisors(s):
                q=s//e
                if not E<=e<2*E or q==1:
                    continue
                for v in vals(n,m,s,e):
                    g=gcd(q,v); l=q//g
                    kernel=F(l*ram(g,m),phi(l))*int(gcd(m,l)==1)
                    direct+=mobius(e)*mobius(q)*mobius(n)*kernel*weight(n,m,s,n*m+e*v)
            grouped=F(0)
            for ep in divisors(s):
                l=s//ep
                mark=sum(ram(g,m) for g in divisors(ep) if E<=ep//g<2*E and g*l>1)
                grouped+=mobius(ep)*mobius(l)*mobius(n)*F(l,phi(l))*int(gcd(m,l)==1)*mark*unitgrid(n,m,s,ep,l)
            self.assertEqual(direct,grouped,(s,E,n,m))
            count+=1
        print("weighted_actual_principal",count)

    def test_ramanujan_positive_m_mass_no_plus_one(self):
        for g,M in product(range(1,101),(F(1,2),F(3,4),F(1),F(7,3),F(8))):
            mass=sum(abs(ram(g,m)) for m in range(1,int(2*M)+1))
            self.assertLessEqual(mass,2*M*len(divisors(g)))
        self.assertEqual(ram(6,0),2) # zero m is not in the positive native support

    def test_axes_are_centered_zero_before_splitting(self):
        for q,t in product((1,2,3,6,30),range(-3,4)):
            self.assertEqual(F(ram(q,0*t),phi(q)),1)
        # Adding the axes is legal only for raw-minus-principal together.

    def test_signed_mark_split_does_not_insert_mu_X(self):
        for F0,C,E in product((1,2,3,6),(1,5,7,15,35),(1,2,5,10)):
            if not mobius(F0*C):
                continue
            ep=F0*C
            direct=sum(mobius(d) for d in divisors(ep) if E<=ep//d<2*E)
            grouped=sum(mobius(d1)*mobius(d2) for d1 in divisors(F0) for d2 in divisors(C)
                        if E<=F0*(C//d2)//d1<2*E)
            self.assertEqual(direct,grouped)
        self.assertNotEqual(mobius(2),mobius(2)*mobius(3))

    def test_h_only_and_delta_only_support_is_not_fp3(self):
        q,u,v=30,2,3
        self.assertEqual(gcd(q,gcd(u,v)),1)
        self.assertGreater(gcd(q,u*v),1)
        self.assertEqual((gcd(q,u),gcd(q,v)),(2,3))
        density=[(-F(u*v,q),F(1)),(F(0),-F(ram(q,u*v),phi(q)))]
        self.assertFalse(roots_equal(density,[]))

    def test_nonunit_and_nonsquarefree_m_survive(self):
        q,e,n,v,m=15,1,1,3,9
        g=gcd(q,v); l=q//g
        raw=l*ram(g,m)*int((n*m+e*v)%l==0)
        principal=F(l*ram(g,m),phi(l))*int(gcd(m,l)==1)
        self.assertEqual(raw-principal,-F(5,2))
        self.assertGreater(gcd(m,q),1)
        self.assertEqual(mobius(m),0)

    def test_signed_mark_must_not_be_unsigned(self):
        ep,E=2,1
        signed=sum(mobius(d) for d in divisors(ep) if E<=ep//d<2*E)
        unsigned=sum(1 for d in divisors(ep) if E<=ep//d<2*E)
        self.assertEqual(signed,-1)
        self.assertEqual(unsigned,1)

    def test_actual_nontrivial_canonical_support(self):
        from sympy import isprime
        T=10**6; M=K=1000
        e,a,b,p,r=32000011,2,3,10007,10009
        q=p*r
        s,n=19230738706564158,19230738706564183
        self.assertTrue(all(isprime(x) for x in (e,a,b,p,r,n)))
        self.assertEqual(s,a*b*e*q)
        h,delta=a*e,b*e
        self.assertEqual(gcd(s,gcd(h,delta)),e)
        self.assertEqual(gcd(s,h)//e,a)
        self.assertEqual(gcd(s,delta)//e,b)
        self.assertEqual(gcd(s,h*delta),a*b*e)
        self.assertEqual(gcd(s,n),1)
        self.assertTrue(s<n<2*s)
        self.assertLessEqual(2*s,T**3//2)
        self.assertTrue(T**687<=e**550<2**550*T**687)
        x=F(3*K,4); y=(n*x+delta)/s
        self.assertTrue(F(K,2)<y<2*K)
        self.assertLessEqual(h*delta*T,s*s)
        self.assertLessEqual(M*K,T)

    def test_unmasked_zero_has_no_m_modulus_sparsity(self):
        for T,q in product((4,9,25),(1,2,3,7)):
            R=S=T**3
            M=F(1); K=F(T)
            Ep=F(S,q)
            count=R*Ep*q*M
            # Squared physical normalization before the common T^-12.
            actual2=count**2*q*q*F(T*T)*K/M/F(R*S**3)
            expected2=F(T*T)*F(R*M*K,S)*q*q
            self.assertEqual(actual2,expected2)
            if q>1:
                self.assertNotEqual(actual2,expected2/(q*q))

    def test_full_low_high_eta_ledger(self):
        kappa,delta=F(1,62),F(3,31)
        for eta in (F(687,550),F(5,4)):
            z=5-4*eta
            high=(F(1),2-eta,F(5,2)-3*eta/2,F(7,2)-2*eta-z/2)
            low_base=(F(7,2)-2*eta,F(5,2)-3*eta/2,
                      F(5,2)-2*eta,F(3,2)-3*eta/2)
            gain=kappa+delta*(1-eta)+(F(3,2)+2*delta)*z
            residual=-1+F(3,2)*z
            self.assertTrue(all(x<=1 for x in high))
            self.assertTrue(all(x+gain<=1 and x+residual<=1 for x in low_base))
            self.assertEqual(low_base[0]+gain,F(749,62)-F(275,31)*eta)
        eta=F(6,5); z=5-4*eta
        worst=F(7,2)-2*eta+kappa+delta*(1-eta)+(F(3,2)+2*delta)*z
        self.assertGreater(worst,1)

    def test_published_scope_and_control_bytes(self):
        note=Path(__file__).resolve().parents[1]/"docs/research/2026-08-31-physical-common-gcd-full-reassembly.md"
        data=note.read_bytes()
        self.assertFalse(any(c<32 and c not in (9,10) for c in data))
        text=data.decode()
        for marker in ("先在完整 centered 差中补回两轴", "dq'>1",
                       "不新增 (Z,f)=1", "不添加 (w,g)=1",
                       "没有** AM5", "687/550", "q₀=1", "CG18"):
            self.assertIn(marker,text)

if __name__=="__main__":
    unittest.main()
