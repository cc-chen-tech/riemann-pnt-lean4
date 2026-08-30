"""Exact finite guards for the rough-modulus full-h/delta reassembly.

Run with pytest/numpy/python-flint/sympy/mpmath available, e.g. the repository
validation environment. These identities and negative fixtures do not certify
the analytic integration-by-parts or primitive large-sieve arguments.
"""
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt
import unittest
from check_physical_large_gcd_type_columns import mobius, phi, units
from check_physical_squarefree_type_descent import divisors
from check_physical_centered_conductor_split import roots_equal


def rough(n, cutoff):
    return n == 1 or all(p >= cutoff for p in divisors(n)
                         if p > 1 and all(p % t for t in range(2, isqrt(p)+1)))


def ram(n, j):
    return sum(d*mobius(n//d) for d in divisors(gcd(n, j)))


def weight(n, m, s, z):
    # A joint rational test weight in native variables, not a weight in v.
    return F(n*m+s+z*z, 1+n*s+m*z) if 1 <= z <= 3*s else F(0)


def grid(n, m, s, eb, d):
    if gcd(m, d) > 1:
        return F(0)
    lo = (1-n*m+eb-1)//eb
    hi = (3*s-n*m)//eb
    return sum((weight(n, m, s, n*m+eb*w)
                for w in range(lo, hi+1) if (n*m+eb*w) % d == 0), F(0))


class ProperDivisorChecks(unittest.TestCase):
    def test_affine_unit_dft_exact(self):
        count = 0
        for d, ell, n, e, m in product((1,2,3,5,6), (1,2,3,5,6,7), (1,7), (1,11), (1,2,3)):
            q = d*ell
            if gcd(d,ell)>1 or gcd(n*e,q)>1:
                continue
            for j in range(-2, q+1):
                left = [(F(j*v,q), F(1)) for v in range(q)
                        if gcd(v,q)==1 and (n*m+e*v)%d==0]
                right = ([(F(-j*n*m*pow(e*ell,-1,d),d), F(ram(ell,j)))]
                         if gcd(m,d)==1 else [])
                self.assertTrue(roots_equal(left,right), (d,ell,n,e,m,j))
                count += 1
        print('exact_affine_DFT',count)

    def test_reciprocity_cancels_native_chirp(self):
        for d, ell, e, j, n, m in product((1,2,3,5), (1,2,3,7), (1,5,11), (-2,1,3), (1,2), (1,3)):
            if gcd(d,e*ell)>1:
                continue
            original = -F(j*n*m*pow(e*ell,-1,d),d)+F(j*n*m,e*d*ell)
            reciprocal = F(j*n*m*pow(d,-1,e*ell),e*ell)
            self.assertEqual((original-reciprocal)%1,0)

    def test_every_cofactor_unit_term_is_retained(self):
        count=0
        for q,e,n,m in product((6,10,15,21,30,35), (1,11), (1,13), (1,2,3)):
            if gcd(e*n,q)>1:
                continue
            s=e*q
            for d in divisors(q):
                ell=q//d
                lo=(1-n*m+e-1)//e
                hi=(3*s-n*m)//e
                direct=sum((weight(n,m,s,n*m+e*v) for v in range(lo,hi+1)
                            if gcd(v,q)==1 and (n*m+e*v)%d==0),F(0))
                expanded=sum((mobius(b)*grid(n,m,s,e*b,d) for b in divisors(ell)),F(0))
                self.assertEqual(direct,expanded,(q,e,n,m,d))
                count+=1
        print('exact_physical_unit_IE',count)

    def test_native_weight_and_mobius_after_full_cofactor(self):
        for e,d,ell,n,m,w in product((1,2,3,5), (2,3,7), (2,3,5), (1,11), (1,2), (-1,1,2)):
            if not mobius(e*d*ell):
                continue
            ep=e*ell
            self.assertEqual(mobius(e)*mobius(d)*mobius(ell),mobius(ep)*mobius(d))
            self.assertEqual(F(n*m+e*ell*w,e*d*ell), F(n*m+ep*w,ep*d))
            self.assertEqual(weight(n,m,e*d*ell,n*m+e*ell*w),weight(n,m,ep*d,n*m+ep*w))

    def test_all_proper_main_terms_reassemble_before_absolute_values(self):
        count=0
        for s,E,n,m,cutoff in product((30,42,70,105,210), (1,2,4,8), (1,11), (1,2,3), (2,3,5)):
            if gcd(n,s)>1:
                continue
            direct=F(0)
            for e in divisors(s):
                q=s//e
                if not(E<=e<2*E and q>1 and rough(q,cutoff)):
                    continue
                for d in divisors(q):
                    ell=q//d
                    if d>1 and ell>1:
                        direct+=mobius(e)*mobius(d)*mobius(ell)*d*grid(n,m,s,e*ell,d)
            grouped=F(0)
            for ep in divisors(s):
                d=s//ep
                if d<=1 or not rough(d,cutoff):
                    continue
                beta=sum(1 for ell in divisors(ep) if ell>1 and rough(ell,cutoff) and E<=ep//ell<2*E)
                self.assertLessEqual(beta,len(divisors(ep)))
                grouped+=beta*mobius(ep)*mobius(d)*d*grid(n,m,s,ep,d)
            self.assertEqual(direct,grouped,(s,E,n,m,cutoff))
            count+=1
        print('exact_marked_reassembly',count)

    def test_prime_cofactor_is_not_assumed(self):
        self.assertTrue(rough(35,5))
        self.assertEqual([35//b for b in divisors(35) if b<35],[35,7,5])
        for ell in (5,7,35,77,385):
            for b in divisors(ell):
                if b<ell:
                    self.assertGreaterEqual(ell//b,5)

    def test_no_false_unit_m_at_omitted_cofactor(self):
        # d=2,l=3,m=3 gives valid v=1,n=e=1, while (m,l)>1.
        self.assertEqual((3+1)%2,0)
        self.assertEqual(gcd(1,6),1)
        self.assertGreater(gcd(3,3),1)

    def test_marked_top_all_four_time_mean_terms(self):
        for eta in (F(5,4),F(7,4),F(2),F(5,2),F(3)):
            low=(F(7,2)-2*eta,F(5,2)-F(3,2)*eta,F(5,2)-2*eta,F(3,2)-F(3,2)*eta)
            high=(F(1),2-eta,F(5,2)-F(3,2)*eta,F(7,2)-2*eta)
            self.assertLessEqual(max(low+high),1)
        self.assertGreater(F(7,2)-2*F(6,5),1)

    def test_affine_poisson_frequency_and_physical_error_cost(self):
        for e,d,ell,b in product((1,3),(1,2,5),(6,35),(1,2,3,5,6,7,35)):
            if ell%b:
                continue
            q=d*ell
            self.assertEqual(F(q,b*d),F(ell,b))
            self.assertEqual(d*F(ell,b),F(q,b))
        eta,J=F(687,550),12
        exponent=1+F(1,2)+(3-eta)-J
        self.assertEqual(exponent,F(9,2)-eta-J)
        self.assertLess(exponent,1)

    def test_frequency_gap_in_normalized_derivative(self):
        for t_over_T,z,j in product((F(1),F(2)),(F(1,2),F(2)),(-3,-1,1,3)):
            # Replace pi by its lower bound 3; Kx/T >= 8.
            if j>0:
                self.assertGreaterEqual(2*3*8*j-t_over_T/z,44)
            else:
                self.assertGreaterEqual(t_over_T/z-2*3*8*j,48)

    def test_actual_composite_physical_support(self):
        from sympy import isprime
        T=10**6
        M=K=1000
        e,p,r=32000011,50021,50101
        s,n=80195295439123331,80195295439123489
        self.assertTrue(all(isprime(z) for z in (e,p,r,n)))
        self.assertEqual(s,e*p*r)
        self.assertGreaterEqual(min(p,r),8*T//K)
        self.assertEqual(gcd(s,n),1)
        self.assertEqual(gcd(s,e*e),e)
        self.assertLessEqual(2*s,T**3//2)
        self.assertTrue(s<n<2*s)
        x=F(3*K,4)
        y=(n*x+e)/s
        self.assertTrue(F(K,2)<y<2*K)
        self.assertLessEqual(M*K,T)
        self.assertLessEqual(e*e*T,s*s)
        self.assertTrue(T**687<=e**550, 'e must lie above the exact E endpoint')
        self.assertTrue(e**550<2**550*T**687, 'e must lie below the exact 2E endpoint')

    def test_small_cofactor_can_retain_a_stationary_frequency(self):
        T,K,freq=64,8,2
        # 3 < pi < 22/7 brackets the critical y=T/(2*pi*freq).
        low=F(T,2*freq)/F(22,7)
        high=F(T,2*freq)/3
        self.assertTrue(F(K,2)<low<high<2*K)
        self.assertLess(freq,8*T//K)

    def test_extra_original_q_box_would_couple_the_mark_to_d(self):
        ep,E=30,2
        def mark(d):
            return sum(1 for ell in divisors(ep)
                       if ell>1 and E<=ep//ell<2*E and 40<=d*ell<80)
        self.assertEqual(gcd(ep,7*11),1)
        self.assertEqual(mark(7),1)
        self.assertEqual(mark(11),0)

if __name__=='__main__':
    unittest.main()
