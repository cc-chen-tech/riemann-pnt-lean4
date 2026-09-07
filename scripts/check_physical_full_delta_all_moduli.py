"""Finite algebra/support/cost guards ONLY; analytic bounds are not certified."""
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt
import unittest

from check_physical_large_gcd_type_columns import mobius, phi
from check_physical_squarefree_type_descent import divisors
from check_physical_centered_conductor_split import roots_equal
from check_physical_full_delta_rough_moduli import weight, grid
from check_physical_reciprocal_principal_band import ie


def colour(q,m,k):
    return sum(mobius(q//(a*b)) for a in divisors(q) for b in divisors(q//a)
               if m%a==0 and k%b==0)


class AllModuliChecks(unittest.TestCase):
    def test_frequency_multiplier_and_three_colours(self):
        count=0
        for q in range(2,61):
            if not mobius(q):
                continue
            for m,k in product(range(1,14),range(-13,14)):
                g=gcd(q,m)
                direct=sum(mobius(q//x) for x in divisors(q)
                           if k%x==0 and gcd(m,q//x)==1)
                reduced=mobius(q//g) if k%g==0 and gcd(k//g,q//g)==1 else 0
                self.assertEqual(direct,reduced)
                self.assertEqual(direct,colour(q,m,k))
                count+=1
        print('three_colour_exact_cases',count)

    def test_full_raw_weighted_physical_reassembly(self):
        count=0
        for s,E,n,m in product((30,42,70,105,210),(1,2,4,8),(1,11),(1,2,3)):
            if gcd(n,s)>1:
                continue
            direct=F(0)
            for e in divisors(s):
                q=s//e
                if not E<=e<2*E or q==1:
                    continue
                for v in range((1-n*m+e-1)//e,(3*s-n*m)//e+1):
                    if gcd(v,q)>1:
                        continue
                    raw=sum(mobius(d)*d for d in divisors(gcd(q,n*m+e*v)))
                    direct+=mobius(e)*mobius(n)*raw*weight(n,m,s,n*m+e*v)
            grouped=F(0)
            for ep in divisors(s):
                qp=s//ep
                mark=sum(1 for b in divisors(ep)
                         if E<=ep//b<2*E and b*qp>1)
                inner=sum((mobius(d)*d*grid(n,m,s,ep,d) for d in divisors(qp)),F(0))
                grouped+=mark*mobius(ep)*mobius(n)*inner
            self.assertEqual(direct,grouped,(s,E,n,m))
            count+=1
        print('full_raw_weighted_reassembly',count)

    def test_affine_fourier_with_native_continuous_phase(self):
        count=0
        for ep,q,n,m,k in product((1,2,3,5),(1,2,3,5,6,10),(1,7),(1,2,3),(-2,-1,0,1,2)):
            if gcd(ep*n,q)>1 or gcd(n,ep)>1:
                continue
            left=[]
            for d in divisors(q):
                if gcd(m,d)>1:
                    continue
                for w in range(q):
                    if (n*m+ep*w)%d==0:
                        left.append((F(k*(n*m+ep*w),ep*q),F(mobius(d)*d)))
            right=[(F(k*n*m*pow(q,-1,ep),ep),F(q*colour(q,m,k)))]
            self.assertTrue(roots_equal(left,right),(ep,q,n,m,k))
            count+=1
        print('native_affine_fourier',count)

    def test_reciprocity_three_colours_cancel_a_b(self):
        for ep,a,b,c,n,z,j in product((1,5,7),(1,2,3),(1,2,3),(1,2,5),(1,11),(1,2),(-1,0,2)):
            q=a*b*c
            if not mobius(q) or gcd(ep,q)>1:
                continue
            original=F((b*j)*n*(a*z)*pow(q,-1,ep),ep)
            reduced=F(n*z*j*pow(c,-1,ep),ep)
            self.assertEqual((original-reduced)%1,0)

    def test_native_kernel_coordinate_and_outer_prefactor(self):
        for ep,a,b,c,n,z,y in product((3,7),(1,2,5),(1,3),(1,2,7),(11,13),(1,2),(F(3,2),F(5,3))):
            q=a*b*c
            s=ep*q
            sp=ep*c
            m=a*z
            yp=b*y
            self.assertEqual(F(s,n*m)/b,F(sp,n*z))
            self.assertEqual(m*y,F(a,b)*z*yp)
            # Square positive factors, keeping the full 1/(ab) outside.
            original=F(q*q,n*s*s*s)*F(1,a*b)
            transformed=F(1,a*a*b*b)*F(c*c,n*sp*sp*sp)
            self.assertEqual(original,transformed)

    def test_rescaled_normalized_profile_is_the_original_one(self):
        for a,b in product((1,2,11),(1,3,101)):
            T=10000; R=S=T**3; M=K=100
            sp=F(S,a*b); mp=F(M,a); kp=b*K
            self.assertEqual(kp*sp,mp*R)
            self.assertEqual(F(a,b)*mp*kp,M*K)
            self.assertEqual(mp*F(T,kp),F(T,a*b))
        self.assertGreater(F(101,1)*100*100,T)

    def test_marked_squarefree_column_exact_divisor_split(self):
        count=0
        for F0,C,E in product((1,2,3,6,10),(1,5,7,15,21,35),(1,2,5,10)):
            if not mobius(F0*C):
                continue
            ep=F0*C
            original=sum(1 for d in divisors(ep) if E<=ep//d<2*E)
            split=0
            for b1 in divisors(F0):
                for b2 in divisors(C):
                    X=C//b2
                    if E<=F0*X//b1<2*E:
                        self.assertEqual(gcd(b2,X),1)
                        self.assertEqual(phi(C),phi(b2)*phi(X))
                        split+=1
            self.assertEqual(original,split)
            count+=1
        print('marked_column_split',count)

    def test_mark_cost_restores_old_E_not_new_E(self):
        for E,Ep,A,B in product((10,20),(20,40,80),(1,2),(1,3)):
            T=10000
            self.assertEqual(F(T,A*B*Ep)*F(Ep,E),F(T,A*B*E))

    def test_zero_frequency_sparsity_does_not_save_a_modulus(self):
        for q,m in product((1,2,6,10),(1,2,6,10,30)):
            self.assertEqual(colour(q,m,0),int(m%q==0))
        for T,q in product((16,81),(1,2,7)):
            R=S=T**3; M=K=isqrt(T)
            # General MK, with all positive square roots removed by squaring.
            Ep=F(S,q)
            count=R*Ep*q*F(M,q)
            amp2=T*T*F(K,M)
            cost2=count*count*q*q*amp2/F(R*S*S*S)
            expected2=T*T*F(R*M*K,S)
            self.assertEqual(cost2,expected2)
            if q>1:
                self.assertNotEqual(cost2,expected2/F(q*q))

    def test_unmasked_diagonal_cost_has_no_extra_inverse_C(self):
        for a,b,C in product((1,2),(1,3),(1,5,7)):
            T=10000; R=1000000; mp=100; sp=10000; kp=F(mp*R,sp)
            Ep=F(sp,C)
            count=Ep*C*R*F(mp,C)
            coefficient2=F(C*C,a*a*b*b*R*sp*sp*sp)
            amp2=F(T*T,mp*kp)
            cost2=count*count*coefficient2*amp2
            self.assertEqual(cost2,F(T*T,a*a*b*b))
            if C>1:
                self.assertNotEqual(cost2,F(T*T,a*a*b*b*C*C))

    def test_new_v_zero_points_are_not_silently_dropped(self):
        ep,c,n,z,v=5,2,1,2,0
        self.assertEqual((n*z+ep*v)%c,0)
        self.assertEqual(gcd(n,ep*c),1)
        self.assertGreater(gcd(z,c),1)
        self.assertGreater(gcd(v,c),1)

    def test_high_and_low_f_have_different_unit_requirements(self):
        # High f=(n,c): e'=5,n=c=2,z=2 is legal without (z,c).
        ep,n,c,z=5,2,2,2
        self.assertEqual(gcd(ep,n*c*z),1)
        self.assertEqual(gcd(n,c),2)
        self.assertEqual(gcd(z,2),2)
        # Low f divides e'/h; z must remain a unit of e'/h.
        ep,h,f,z=10,1,2,3
        self.assertEqual(ep%(h*f),0)
        self.assertEqual(gcd(z,ep//h),1)
        self.assertEqual(gcd(z,f),1)

    def test_high_unmasked_complete_single_ie(self):
        count=0
        for ep,n,c,z,ab in product(range(1,14),range(1,14),range(1,14),range(1,9),(1,6)):
            if not mobius(ep) or gcd(ep,ab)>1:
                continue
            h=gcd(ep,z); a0=ep//h; Z=z//h
            expected=mobius(ep)*mobius(n)*mobius(c)
            if gcd(n,ep*c*ab)>1 or gcd(c,ep*ab)>1:
                expected=0
            actual=0
            for f in divisors(gcd(n,c)):
                x,y=n//f,c//f
                if (gcd(f,ep*ab)>1 or gcd(x,f*ep*ab)>1
                        or gcd(y,f*ep*ab)>1 or gcd(Z,a0)>1):
                    continue
                actual+=mobius(h)*mobius(a0)*mobius(f)*mobius(x)*mobius(y)
            self.assertEqual(actual,expected,(ep,n,c,z,ab))
            count+=1
        print('unmasked_high_single_IE',count)

    def test_low_unmasked_complete_three_ie(self):
        count=0
        for h,d,ell,k,Z,ab in ((1,1,1,1,2,1),(1,1,1,3,2,6),(2,3,5,7,3,7)):
            D0=h*k*Z*ell*ab
            Dn=Dq=h*d*ell*ab
            for b,n,q in product(range(1,18),range(1,13),range(1,13)):
                expected=F(mobius(b)**2*mobius(n)*mobius(q),phi(b))
                if (gcd(b,D0*n*q)>1 or gcd(n,Dn*q)>1 or gcd(q,Dq)>1):
                    expected=F(0)
                self.assertEqual(ie(b,n,q,D0,Dn,Dq),expected,(b,n,q,D0,Dn,Dq))
                count+=1
        print('unmasked_low_three_IE',count)

    def test_endpoint_and_general_scale_exponents(self):
        kappa,delta=F(1,62),F(3,31)
        eta=F(687,550); lam=5-4*eta
        count=0
        for etap,aa,bb in product((eta,F(5,4),F(3,2),F(2),F(5,2)),(F(0),F(1,4),F(1,2)),(F(0),F(1,4),F(1,2),F(1))):
            f=aa+bb
            if etap+f>3:
                continue
            base=(F(7,2)-2*etap-f,F(5,2)-F(3,2)*etap-f/2,
                  F(5,2)-2*etap-f,F(3,2)-F(3,2)*etap-f/2)
            gain=kappa+delta*(1-eta-f)+(F(3,2)+2*delta)*lam
            low=[x+gain for x in base]+[x-1+F(3,2)*lam for x in base]
            high=(F(1),2-etap,F(5,2)-F(3,2)*etap-f,F(7,2)-2*etap-f-lam/2)
            self.assertLessEqual(max(low+list(high)),1,(etap,aa,bb))
            count+=1
        self.assertEqual(F(7,2)-2*eta+kappa+delta*(1-eta)+(F(3,2)+2*delta)*lam,1)
        print('general_scale_exponent_cases',count)

    def test_genuine_small_prime_physical_support(self):
        from sympy import isprime
        T=10**6
        M=K=1000
        e,p,r=32000011,50021,50101
        s,n=160390590878246662,160390590878246669
        q=2*p*r
        self.assertTrue(all(isprime(x) for x in (e,p,r,n)))
        self.assertEqual(s,e*q)
        self.assertEqual(gcd(s,n),1)
        self.assertEqual(gcd(e,q),1)
        self.assertLess(2,8*T//K)
        self.assertEqual(gcd(s,e*e),e)
        self.assertTrue(s<n<2*s)
        self.assertLessEqual(2*s,T**3//2)
        x=F(3*K,4)
        y=(n*x+e)/s
        self.assertTrue(F(K,2)<y<2*K)
        self.assertLessEqual(M*K,T)
        self.assertLessEqual(e*e*T,s*s)
        self.assertTrue(T**687<=e**550)
        self.assertTrue(e**550<2**550*T**687)

    def test_qprime_one_requires_old_q_greater_than_one(self):
        # At finite heights the exact mark contains b*qprime>1.
        ep,E,qp=6,1,1
        mark=sum(1 for b in divisors(ep) if E<=ep//b<2*E and b*qp>1)
        self.assertEqual(mark,1)
        ep,E=1,1
        mark=sum(1 for b in divisors(ep) if E<=ep//b<2*E and b*qp>1)
        self.assertEqual(mark,0)


if __name__=='__main__':
    unittest.main()
