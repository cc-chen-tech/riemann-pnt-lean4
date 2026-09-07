"""Exact finite guards for the native m/k low-conductor projection.

These do not prove the analytic large sieve, tails, or a zero-free theorem.
"""
from fractions import Fraction as F
from itertools import product
from math import gcd
import unittest

from check_physical_large_gcd_type_columns import mobius
from check_physical_squarefree_type_descent import divisors
from check_physical_low_conductor_common_large_sieve import low_exponents, high_exponents


def overlap_exponents(eta, gamma, ep=None):
    main, rest = low_exponents(eta, ep)
    return tuple(x-F(7,6)*gamma for x in main), tuple(x-gamma for x in rest)


def count_overlap(m, radius, threshold):
    stop = int(2*radius)
    return sum(gcd(m, r) >= threshold for r in range(-stop, stop+1) if r)


class NativeOverlapChecks(unittest.TestCase):
    def test_original_unit_makes_gcd_identity_exact(self):
        count = 0
        for h, d, z in product(range(1,31), range(1,31), range(1,21)):
            if not mobius(h*d) or gcd(d,z) != 1:
                continue
            for r in range(-30,31):
                if not r:
                    continue
                self.assertEqual(gcd(h*z,d*r), gcd(h*z,r))
                count += 1
        self.assertEqual(count,241740)

    def test_d_z_unit_cannot_be_dropped(self):
        h,d,z,r = 1,2,2,1
        self.assertNotEqual(gcd(h*z,d*r),gcd(h*z,r))

    def test_h_d_coprimality_cannot_be_dropped(self):
        h,d,z,r = 2,2,1,1
        self.assertNotEqual(gcd(h*z,d*r),gcd(h*z,r))

    def test_signed_r_union_bound_has_no_extra_one(self):
        count = 0
        for m,R,G in product(range(1,181), (F(1,2),F(1),F(3,2),F(3),F(7),F(19),F(40)),
                             (F(1),F(3,2),F(2),F(5),F(11),F(41))):
            ds=divisors(m)
            union=sum(2*int(2*R/g) for g in ds if g>=G)
            self.assertLessEqual(count_overlap(m,R,G),union)
            self.assertLessEqual(union,4*R*len(ds)/G)
            count += 1
        self.assertEqual(count,7560)

    def test_short_nonempty_r_cannot_be_created(self):
        for m,R,G in product(range(1,50),(F(1,8),F(1,2),F(1)),(F(3),F(8))):
            self.assertEqual(count_overlap(m,R,G),0)

    def test_r_sign_is_counted_twice(self):
        self.assertEqual(count_overlap(6,F(3),F(2)),8)
        self.assertEqual(count_overlap(1,F(3),F(2)),0)

    def test_same_filtered_set_also_bounds_d(self):
        for h,d,z,r in product(range(1,12),range(1,12),range(1,8),range(1,20)):
            if gcd(d,h*z)!=1:
                continue
            g=gcd(h*z,d*r)
            self.assertLessEqual(g,abs(r))
            self.assertLessEqual(d*g,abs(d*r))

    def test_native_filter_is_not_hd_filter(self):
        h,d,z,r,b,n,q=2,5,3,2,7,11,13
        ep=h*d*b
        self.assertEqual(gcd(ep,h*z),h)
        self.assertEqual(gcd(ep//h,d*r),d)
        self.assertEqual(gcd(b,z*r),1)
        self.assertEqual(gcd(n,ep*q),1)
        self.assertEqual(gcd(h*z,d*r),2)
        self.assertEqual(gcd(ep,h*z*d*r),10)
        self.assertNotEqual(gcd(h*z,d*r)>=3,gcd(ep,h*z*d*r)>=3)

    def test_large_overlap_does_not_delete_nonsquarefree_product(self):
        m,k=6,10
        self.assertEqual(gcd(m,k),2)
        self.assertEqual(mobius(m*k),0)
        self.assertNotEqual(mobius(7),0)  # The original Mobius integer is n, not mk.

    def test_y_z_mask_stays_removed(self):
        # Actual AM12/LC3: a permissible Y can divide z.
        F0,ell,Y,z=1,5,3,3
        actual=mobius(Y)*int(gcd(Y,F0*ell)==1)
        self.assertEqual(actual,-1)
        self.assertNotEqual(actual,actual*int(gcd(Y,z)==1))

    def test_eight_terms_at_gamma_one_tenth(self):
        main,rest=overlap_exponents(F(6,5),F(1,10))
        self.assertEqual(main,(F(59,60),F(3,4),F(3,20),-F(1,20)))
        self.assertEqual(rest,(F(0),-F(3,10),-F(9,10),-F(11,10)))

    def test_exact_threshold_and_open_complement(self):
        for gamma in (F(0),F(1,20),F(3,35),F(1,10),F(1,4),F(1,2)):
            main,rest=overlap_exponents(F(6,5),gamma)
            self.assertEqual(max(main+rest)<=1,gamma>=F(3,35))
        self.assertEqual(low_exponents(F(6,5))[0][0],F(11,10))
        self.assertEqual(high_exponents(F(6,5)),(F(1),F(4,5),F(7,10),F(1)))

    def test_larger_Eprime_does_not_worsen_any_term(self):
        for ep in (F(6,5),F(3,2),F(2),F(3)):
            main,rest=overlap_exponents(F(6,5),F(1,10),ep)
            self.assertTrue(all(x<=F(59,60) for x in main+rest))
        self.assertEqual(len(overlap_exponents(F(6,5),F(1,10),F(3))[0]),4)

    def test_density_and_shortened_d_sum_are_distinct(self):
        gamma=F(1,10)
        self.assertEqual(F(11,10)-gamma-F(1,6)*gamma,F(59,60))
        self.assertNotEqual(F(11,10)-F(1,6)*gamma,F(59,60))
        self.assertNotEqual(F(11,10)-gamma,F(59,60))

    def test_signed_old_shell_mark_is_retained(self):
        # e'=30,E=5: allowed mark divisors are 5,6, with signs -1,+1.
        self.assertEqual(sum(mobius(d) for d in divisors(30) if 5<=30//d<10),0)
        self.assertEqual(sum(abs(mobius(d)) for d in divisors(30) if 5<=30//d<10),2)

    def test_full_large_frequency_ring_still_summable(self):
        self.assertLess(1+F(1,6)+F(1,100)-12,-1)
        for v,G,D in product((F(1),F(3),F(16)),(F(1),F(7)),(F(2),F(11))):
            for d in range(1,31):
                admissible=[r for r in range(-100,101) if r and G<=abs(r) and abs(d*r)<=2*v*D]
                if admissible:
                    self.assertLessEqual(d,2*v*D/G)

    def test_native_internal_fixture(self):
        from sympy import isprime
        g,p,d,b,q,n=7,101,103,1009,19322369063,2366229842790922513
        self.assertTrue(all(v<2**64 and isprime(v) for v in (g,p,d,b,q,n)))
        self.assertEqual(len({g,p,d,b,q,n}),6)
        h,m,k=g*p,g*p,g*d
        A,ep=h*d,h*d*b
        T=7*m*k
        s=ep*q
        self.assertEqual((T,ep,A),(3568229,73476389,72821))
        self.assertTrue(T**6<=ep**5<32*T**6)
        self.assertEqual((gcd(ep,m),gcd(ep//h,k)),(h,d))
        self.assertEqual(gcd(m,k),g)
        self.assertGreaterEqual(g**10,T)
        self.assertGreater(A**3,T**2)
        self.assertEqual(gcd(n,ep*q),1)
        self.assertTrue(s<n<2*s<=T**3//2)
        M=K=m
        y=F(n*m,s)
        self.assertTrue(K<y<2*K)
        self.assertTrue(F(1,8)<F(M*K,T)<F(1,2))
        self.assertTrue(T<6*F(m*k*n,s))
        self.assertLess(F(44,7)*F(m*k*n,s),2*T)

    def test_zero_mode_is_not_in_this_projection(self):
        self.assertEqual(gcd(12,0),12)
        # A large gcd alone would admit k=0; the explicit exclusion is essential.
        selected=[k for k in range(-4,5) if k and gcd(12,k)>=3]
        self.assertNotIn(0,selected)
        self.assertEqual(selected,[-4,-3,3,4])


if __name__=='__main__':
    unittest.main()
