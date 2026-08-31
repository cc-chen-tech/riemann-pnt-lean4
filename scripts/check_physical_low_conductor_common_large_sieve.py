"""Finite guards for the low-conductor common-column proof.

These do not prove hybrid LS, the log exponent pair, or zero exclusion.
"""
from fractions import Fraction as F
from itertools import product
from math import gcd
import unittest

from check_physical_large_gcd_type_columns import mobius, phi
from check_physical_squarefree_type_descent import divisors

KAPPA, DELTA = F(1,30), F(1,6)
POWERS = (F(-1,2), F(1,2), F(1,2), F(3,2))

def low_exponents(eta, ep=None):
    if ep is None:
        ep=eta
    z=max(F(0),5-4*eta)
    base=(F(7,2)-2*ep,F(5,2)-3*ep/2,F(5,2)-2*ep,F(3,2)-3*ep/2)
    main=tuple(b+KAPPA+DELTA*(1-eta)+max(F(0),p+2*DELTA)*z
               for b,p in zip(base,POWERS))
    remainder=tuple(b-1+max(F(0),p)*z for b,p in zip(base,POWERS))
    return main,remainder

def high_exponents(eta,ep=None):
    if ep is None:
        ep=eta
    z=max(F(0),5-4*eta)
    return (F(1),2-ep,F(5,2)-3*ep/2,F(7,2)-2*ep-z/2)

def normalized_weights(h,ell,d,f,l,j,C,X,Y,Ep,Qp,R):
    c=F(h*ell*d*f*l*C,Ep)
    x=F(f*j*X,R)
    y=F(l*j*Y,Qp)
    return c,x,y

class LowCommonChecks(unittest.TestCase):
    def test_conductor_mask_is_entirely_character_zero_extension(self):
        count=0
        for ell,F0,X,Y,z in product((1,3,5,7,15,21),(1,2,6,10),range(1,31),range(1,21),(1,2)):
            old_x=mobius(X)*int(gcd(X,F0*ell)==1)
            new_x=mobius(X)*int(gcd(X,F0)==1)*int(gcd(X,ell)==1)
            old_y=mobius(Y)*int(gcd(Y,F0*ell)==1)
            new_y=mobius(Y)*int(gcd(Y,F0)==1)*int(gcd(Y,ell)==1)
            self.assertEqual((old_x,old_y),(new_x,new_y))
            # AM12/LC3 removed the old (Y,z) restriction.  Equality of two
            # identically overmasked columns alone cannot guard this fact.
            if gcd(Y,F0*ell)==1:
                self.assertEqual(old_y,mobius(Y))
                self.assertEqual(new_y,mobius(Y))
            count+=1
        print("common_character_masks",count)

    def test_no_forbidden_C_X_or_C_Y_mask(self):
        C,X,Y=3,3,1
        self.assertEqual(mobius(C)**2*mobius(X)*mobius(Y),-1)
        self.assertNotEqual(-1,-1*int(gcd(C,X)==1))
        C,X,Y=3,1,3
        self.assertEqual(mobius(C)**2*mobius(X)*mobius(Y),-1)
        self.assertNotEqual(-1,-1*int(gcd(C,Y)==1))

    def test_ell_uniform_actual_s_and_n_weight_coordinates(self):
        count=0
        for h,ell,d,f,l,j,C,X,Y in product((1,2),(1,3,5),(1,7),(1,2),(1,3),(1,5),(1,11),(1,7),(1,13)):
            Ep,Qp,R=F(256),F(4096),F(16384)
            c,x,y=normalized_weights(h,ell,d,f,l,j,C,X,Y,Ep,Qp,R)
            ep=h*ell*d*f*l*C
            n=f*j*X
            q=l*j*Y
            self.assertEqual(n,R*x)
            self.assertEqual(ep*q,Ep*Qp*c*y)
            # Arbitrary nonseparable polynomial probe in the native arguments.
            native=F(n,R)**2 + F(ep*q,Ep*Qp)**3 + F(n*ep*q,R*Ep*Qp)
            common=x*x+(c*y)**3+x*c*y
            self.assertEqual(native,common)
            count+=1
        print("native_common_weight_coordinates",count)

    def test_one_gauss_factor_and_phi_normalization(self):
        for ell in (3,5,7,15,21,35,105):
            # [sqrt(ell)/phi(ell)]^2 = ell^-1 [ell/phi(ell)]^2.
            lhs=F(ell,phi(ell)**2)
            rhs=F(1,ell)*F(ell,phi(ell))**2
            self.assertEqual(lhs,rhs)
            self.assertNotEqual(lhs,rhs/ell)

    def test_four_terms_match_bilinear_LS_square(self):
        for N1,N2,T,L in product((F(1),F(7),F(101)),repeat=4):
            exact=N1*N2*(L*L*T+N1)*(L*L*T+N2)/L
            squares=((N1*N2)**2/L,L*T*N1*N1*N2,
                     L*T*N1*N2*N2,L**3*T*T*N1*N2)
            self.assertEqual(exact,sum(squares))
            self.assertGreater(exact,sum(squares[:3]))
        self.assertEqual(POWERS,(F(-1,2),F(1,2),F(1,2),F(3,2)))

    def test_full_f_l_j_costs_are_summable(self):
        # Include 1/phi(f)1/phi(l); this table concerns powers only.
        for delta in (F(0),DELTA,F(1,2)):
            exponents=((delta-2,delta-2,F(-2)),
                       (delta-2,delta-F(3,2),-F(3,2)),
                       (delta-F(3,2),delta-2,-F(3,2)),
                       (delta-F(3,2),delta-F(3,2),F(-1)))
            self.assertTrue(all(v<=-1 for row in exponents for v in row))

    def test_actual_signed_mark_split_for_varying_conductor(self):
        count=0
        for h,ell,d,f,l,C,E in product((1,2),(1,3,5),(1,7),(1,11),(1,13),(1,17,19,17*19),(1,5,19,100)):
            F0=h*ell*d*f*l
            if not mobius(F0*C):
                continue
            ep=F0*C
            old=sum(mobius(b) for b in divisors(ep) if E<=ep//b<2*E)
            split=sum(mobius(b1)*mobius(b2) for b1 in divisors(F0) for b2 in divisors(C)
                      if E<=F0*(C//b2)//b1<2*E)
            self.assertEqual(old,split)
            count+=1
        print("varying_ell_signed_old_E_marks",count)

    def test_old_E_cost_is_paid_before_replacement(self):
        for T,E,Ep in product((F(16),F(81)),(F(2),F(7)),(F(8),F(32))):
            if Ep<E:
                continue
            H0=Ep/E
            self.assertEqual(T/Ep*H0,T/E)
            if Ep>E:
                self.assertNotEqual(T/Ep,T/E)

    def test_principal_is_one_conductor_not_every_modulus(self):
        family=[(ell,"primitive") for ell in (1,3,5,7,15)]
        self.assertEqual(sum(ell==1 for ell,_ in family),1)
        self.assertNotEqual(sum(ell==1 for ell,_ in family),len(family))
        self.assertEqual(POWERS[0]+2*DELTA,-F(1,6))

    def test_exact_eta_endpoint_all_eight_low_terms_and_high(self):
        eta=F(81,65)
        a,b=low_exponents(eta)
        h=high_exponents(eta)
        self.assertEqual(a[0],1)
        self.assertEqual(h[-1],1)
        self.assertEqual(5-4*eta,F(1,65))
        self.assertTrue(all(x<=1 for x in a+b+h))
        print("eta=81/65: main",a,"remainder",b,"high",h)
        for i in range(101):
            eta=F(81,65)+i*(F(5,4)-F(81,65))/100
            for ep in (eta,(eta+3)/2,F(3)):
                main,rem=low_exponents(eta,ep)
                self.assertTrue(all(x<=1 for x in main+rem+high_exponents(eta,ep)))

    def test_threshold_and_6_over_5_not_closed(self):
        self.assertEqual((F(5,2)+KAPPA+DELTA)/(2+DELTA),F(81,65))
        self.assertGreater(low_exponents(F(81,65)-F(1,10000))[0][0],1)
        self.assertEqual(low_exponents(F(6,5))[0][0],F(11,10))
        self.assertGreater(low_exponents(F(6,5))[0][0],1)
        self.assertEqual(F(687,550)-F(81,65),F(21,7150))

    def test_Eprime_and_short_Q_are_not_discarded(self):
        eta=F(81,65)
        a,b=low_exponents(eta,F(3))
        # The fourth short-short term is nonzero even if Q'=1.
        self.assertEqual(len(a),4)
        self.assertEqual(len(b),4)
        self.assertTrue(all(x<=1 for x in a+b))
        # Q'<T makes the long-X/short-Y cross term larger than long-long.
        self.assertGreater(a[1],a[0])
        self.assertEqual(a[3],-F(581,195))

    def test_infinite_frequency_ring_has_strict_margin(self):
        self.assertLess(1+DELTA+F(1,100)-12,0)
        # Nonempty k=d*r !=0: d <= 2vD, and count <=4vD/d; no +1.
        for D,v,d in product((F(1,8),F(1),F(8)),(F(1,4),F(1),F(16)),range(1,21)):
            count=sum(v*D<=abs(d*r)<2*v*D for r in range(-300,301) if r)
            self.assertLessEqual(count,4*v*D/d)

    def test_native_canonical_integer_support_below_old_line(self):
        from sympy import isprime
        T=10**6
        e=30500003
        q=327868829
        s=60000001608638922
        n=60000001608638989
        K=1000
        h,delta=2*e,3*e
        # Sympy's deterministic primality range; do not certify BPSW-only data.
        self.assertTrue(all(v<2**64 for v in (e,q,n)))
        self.assertTrue(all(isprime(v) for v in (e,q,n)))
        self.assertEqual(s,6*e*q)
        self.assertTrue(T**81<=e**65<2**65*T**81)
        self.assertLess(e**550,T**687)
        self.assertEqual(gcd(s,gcd(h,delta)),e)
        self.assertEqual((gcd(s,h)//e,gcd(s,delta)//e),(2,3))
        self.assertEqual(gcd(n,s),1)
        self.assertTrue(s<n<2*s<=T**3//2)
        x=F(3*K,4)
        y=(n*x+delta)/s
        self.assertTrue(F(K,2)<y<2*K)
        self.assertLessEqual(h*delta*T,s*s)
        self.assertEqual(K*K,T)
        # This is support, not nonvanishing of an arbitrary W/V integral.

if __name__=="__main__":
    unittest.main()
