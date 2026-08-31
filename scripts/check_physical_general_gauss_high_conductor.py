#!/usr/bin/env python3
"""Finite GH guards; not an analytic large-sieve or full-gate proof."""
from fractions import Fraction as F
from itertools import product
from math import gcd, ceil, sqrt, isqrt
from pathlib import Path
import unittest

from check_physical_centered_conductor_split import characters, roots_equal
from check_physical_large_gcd_type_columns import mobius, phi, units
from check_physical_squarefree_type_descent import divisors


def ram(q, a):
    return sum(d*mobius(q//d) for d in divisors(gcd(q, a)))


def spectral(e, q, n, r, s, high=1):
    terms=[]
    for ell in divisors(e):
        if ell < high:
            continue
        c=e//ell
        for cond, chi in characters(ell):
            if cond != ell or gcd(r*s, ell) != 1:
                continue
            ca=chi[(r*s) % ell]
            coeff=F(mobius(ell)*sum(mobius(d)*d for d in divisors(gcd(c,r*s))),phi(e))
            for y in units(ell):
                phase=F(y,ell)-chi[y]-chi[c % ell]+ca+chi[(-n) % ell]-chi[q % ell]
                terms.append((phase,coeff))
    return terms


def allocated(e,q,n,rho,sigma,low):
    out=[]
    for ell in divisors(e):
        if ell < low: continue
        c=e//ell
        for d in divisors(c):
            if rho*sigma % d: continue
            j=gcd(d,rho); k=d//j
            r=rho//j; s=sigma//k
            assert gcd(r,k)==1
            for cond,chi in characters(ell):
                if cond != ell or gcd(r*s,ell)!=1: continue
                coeff=F(mobius(ell)*mobius(d)*d,phi(e))
                for y in units(ell):
                    phase=F(y,ell)-chi[y]-chi[(c//d)%ell]+chi[(-n)%ell]-chi[q%ell]+chi[r%ell]+chi[s%ell]
                    out.append((phase,coeff))
    return out


class GaussHigh(unittest.TestCase):
    def test_general_gauss_all_nonunit_a(self):
        for e in (2,3,6,10,15,21,30,35):
            for ell in divisors(e):
                c=e//ell
                for cond,chi in characters(ell):
                    if cond!=ell: continue
                    for a in range(e):
                        left=[(F(a*y,e)-chi[y%ell],F(1)) for y in units(e)]
                        right=[] if gcd(a,ell)!=1 else [(F(y,ell)-chi[y]-chi[c%ell]+chi[a%ell],F(ram(c,a))) for y in units(ell)]
                        self.assertTrue(roots_equal(left,right),(e,ell,a))

    def test_primitive_not_induced_at_a(self):
        e,ell,c,a=15,3,5,5
        _,chi=next(x for x in characters(ell) if x[0]==ell)
        rhs=[(F(y,ell)-chi[y]-chi[c%ell]+chi[a%ell],F(ram(c,a))) for y in units(ell)]
        self.assertFalse(roots_equal(rhs,[]))
        self.assertEqual(gcd(a,e),5)

    def test_outer_mu_ramanujan_exact(self):
        for c,a in product((1,2,3,6,10,15,21,30,35,42),range(-30,31)):
            self.assertEqual(mobius(c)*ram(c,a),sum(mobius(d)*d for d in divisors(gcd(c,a))))

    def test_unique_allocation_signed_nonzero(self):
        for d,rho,sigma in product((1,2,3,6,10,15,30),range(-12,13),range(-12,13)):
            if not rho or not sigma: continue
            js=[j for j in divisors(d) if rho%j==0 and sigma%(d//j)==0 and gcd(rho//j,d//j)==1]
            self.assertEqual(js,[gcd(d,rho)] if rho*sigma%d==0 else [])

    def test_false_extra_masks_have_witnesses(self):
        d,rho,sigma=6,2,6
        j=gcd(d,rho); k=d//j
        self.assertEqual(gcd(rho//j,k),1)
        self.assertNotEqual(gcd(sigma//k,j),1)
        d,rho,sigma=6,4,3
        j=gcd(d,rho)
        self.assertNotEqual(gcd(rho//j,j),1)

    def test_full_signed_spectrum_and_split(self):
        for e,q in ((6,13),(15,37),(30,67)):
            for n,r,s in product(units(e)[:4],(-3,1,5),(-2,1,3)):
                if not n: continue
                raw=[(F(-n*r*s*pow(q,-1,e),e),F(mobius(e)))]
                whole=spectral(e,q,n,r,s)
                self.assertTrue(roots_equal(raw,whole))
                self.assertTrue(roots_equal(whole,allocated(e,q,n,r,s,1)))
                for Z in (2,3,5):
                    high=spectral(e,q,n,r,s,Z)
                    self.assertTrue(roots_equal(high,allocated(e,q,n,r,s,Z)))

    def test_nonunit_high_conductor_is_not_zero(self):
        high=spectral(15,37,1,3,1,5)
        self.assertFalse(roots_equal(high,[]))
        self.assertTrue(roots_equal(spectral(15,37,1,3,1,15),[]))

    def test_joint_complex_error_ledger_without_Be(self):
        for e,q in ((6,13),(15,37)):
            original=[]; rebuilt=[]
            for n,r,s in product(range(1,q+4),(-3,1,q),(-2,1,3)):
                if gcd(n,e)!=1: continue
                w=F(mobius(e)*mobius(q)*mobius(n)*(n+e*r-q*s),q*(n+1)*(abs(r)+1)*(abs(s)+1))
                raw=F(n*r*s*pow(e,-1,q),q)
                recip=F(-n*r*s*pow(q,-1,e),e)+F(n*r*s,e*q)
                uq=gcd(r*s,q)==1; un=n%q!=0
                rebuilt.append((recip,w))
                if uq and un:
                    original.extend(((raw,w),(F(0),w/F(q-1))))
                    rebuilt.append((F(0),w/F(q-1)))
                if uq and not un: rebuilt.append((raw,-w))
                if not uq: rebuilt.append((raw,-w))
            self.assertTrue(roots_equal(original,rebuilt))

    def test_chirp_and_normalized_lengths_unchanged(self):
        for c,ell,d,j in ((6,5,6,2),(10,3,5,1),(14,5,7,7)):
            k=d//j; E=c*ell; R=5*E; Q=101; J1=F(15); J2=F(21)
            n,r,s=7,3,4
            self.assertEqual(F(n*j*r*k*s,E*Q),F(d*n*r*s,c*ell*Q))
            self.assertEqual(F(n*j*r*k*s,E*Q),F(n*r*s,ell*Q*(c//d)))
            self.assertEqual(R*J1*J2/(E*Q),R*(J1/j)*(J2/k)*d/(c*ell*Q))

    def test_four_squares_before_summation(self):
        for R,K,L,d,X,ph in product((2,5),(3,7),(1,4),(1,2),(F(1,3),F(9)),(1,4)):
            J=F(1)+X
            actual=F(d*d,ph*ph*L)*R*F(K,d)*(R+L*L*J)*(F(K,d)+L*L*J)/J
            expect=F(R*R*K*K,ph*ph*L)/J+F(d*L*R*R*K+L*R*K*K,ph*ph)+F(d*L**3*R*K,ph*ph)*J
            self.assertEqual(actual,expect)

    def test_divisor_allocation_counts(self):
        for c in (1,2,3,6,10,15,30,42,105,210):
            ds=divisors(c)
            self.assertLessEqual(sum(len(divisors(d)) for d in ds),len(ds)**2)
            self.assertLessEqual(sum(d*len(divisors(d)) for d in ds),c*len(ds)**2)

    def test_high_cost_exponents_and_no_low_claim(self):
        eta=F(6,5); z=F(1,5)
        terms=(F(7,2)-2*eta-z/2,2-eta,F(5,2)-F(3,2)*eta,F(1))
        self.assertEqual(terms,(1,F(4,5),F(7,10),1))
        self.assertEqual(F(7,2)-2*eta,F(11,10))
        for eta in (F(1),F(7,6),F(6,5),F(5,4)):
            z=max(F(0),5-4*eta)
            self.assertLessEqual(z,eta)
            self.assertLessEqual(F(7,2)-2*eta-z/2,1)

    def test_cofactor_phase_cannot_be_deleted(self):
        c,ell,a=5,3,5
        _,chi=next(x for x in characters(ell) if x[0]==ell)
        correct=[(F(y,ell)-chi[y]-chi[c%ell]+chi[a%ell],F(ram(c,a))) for y in units(ell)]
        wrong=[(F(y,ell)-chi[y]+chi[a%ell],F(ram(c,a))) for y in units(ell)]
        self.assertFalse(roots_equal(correct,wrong))

    def test_zero_input_principal_is_not_unit_principal(self):
        for e in (2,3,6,10,15,30):
            principal=F(sum(mobius(d)*d for d in divisors(e)),phi(e))
            self.assertEqual(principal,mobius(e))
            self.assertNotEqual(principal,F(1,phi(e)))

    def test_Z_one_still_excludes_principal(self):
        e,q,n,r,s=15,37,1,3,1
        full=spectral(e,q,n,r,s,1)
        high=spectral(e,q,n,r,s,max(2,1))
        self.assertFalse(roots_equal(full,high))
        self.assertTrue(roots_equal(high,spectral(e,q,n,r,s,2)))

    def test_nonempty_scaled_integer_support(self):
        for J1,J2,d in product((F(1,2),F(1),F(3),F(7)),repeat=3):
            if d.denominator!=1 or d<1: continue
            d=int(d)
            for j in divisors(d):
                k=d//j
                rs=[r for r in range(1,15) if J1/2<=j*r<=2*J1]
                ss=[s for s in range(1,15) if J2/2<=k*s<=2*J2]
                if rs and ss:
                    self.assertGreaterEqual(J1/j,F(1,2))
                    self.assertGreaterEqual(J2/k,F(1,2))
                    self.assertGreaterEqual(J1*J2/d,F(1,4))

    def test_short_X_four_square_ratio(self):
        for R,K,L,d,nu,theta in product((1,3),(2,5),(1,4),(1,3),(1,7),(F(1,8),F(1),F(5))):
            x=nu*theta; kk=K*theta
            actual=R*R*kk*kk/(L*(1+x))+d*L*R*R*kk+L*R*kk*kk+d*L**3*R*kk*(1+x)
            natural=F(R*R*K*K,L*nu)+d*L*R*R*K+L*R*K*K+d*L**3*R*K*nu
            self.assertLessEqual(actual,2*max(theta,theta*theta)*natural)

    def test_original_unbalanced_small_factor_support(self):
        e,q=33,1009
        S=e*q; T=(8*S)**(1/3); A=sqrt(T); H=S/A
        prime=lambda n:n>=2 and all(n%d for d in range(2,isqrt(n)+1))
        n=next(n for n in range(S+1,2*S) if prime(n))
        u=v=ceil(H/e); x=3*A/4; y=(n*x+e*v)/S
        self.assertEqual(mobius(e),1)
        self.assertEqual(mobius(n),-1)
        self.assertEqual(gcd(n,e*q),1)
        self.assertEqual(gcd(u*v,q),1)
        self.assertLessEqual(H,e*u)
        self.assertLessEqual(e*u,2*H)
        self.assertTrue(A/2<=y<=2*A)
        self.assertGreater(11,T**F(1,5))
        self.assertFalse(roots_equal(spectral(e,q,1,3,1,11),[]))

    def test_document_keeps_low_principal_and_original_masks(self):
        text=(Path(__file__).parents[1]/'docs/research/2026-08-31-physical-general-gauss-high-conductor.md').read_text()
        for required in ('F_lo 含所有低导子','χ_ind(5)','(r,k)=1','K/d≥Q/4','log E','EE*、EC*、CE*、CC*','C_{\\rm sf}=F+O_q-B_{nq}-B_{qd}'):
            self.assertIn(required,text)


if __name__=='__main__':
    unittest.main()
