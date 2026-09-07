#!/usr/bin/env python3
"""Finite PII guards, not a proof of smooth Poisson or of the full gate."""
from fractions import Fraction as F
from math import gcd, isqrt, ceil, sqrt
from itertools import product
from collections import defaultdict
import unittest

from check_physical_type_i_triple_completion import triple_spectrum
from check_physical_large_gcd_type_columns import mobius
from check_physical_squarefree_type_descent import divisors
from check_physical_centered_conductor_split import roots_equal


def prime_incidence_spectrum(q, a, B, k, r, s):
    if q < 2 or any(q % p == 0 for p in range(2, isqrt(q)+1)) or gcd(a*B, q) != 1:
        raise ValueError('prime q and unit a,B required')
    if gcd(k*r*s, q) != 1:
        return F(0)
    return q*q*(int((a*k+B*r*s) % q == 0)-F(1, q-1))


def resonance_pairs(a, B, limit):
    if a < 1 or B < 1 or gcd(a, B) != 1:
        raise ValueError('positive coprime a,B required')
    out = set()
    for t in range(-limit//B, limit//B+1):
        if not t or abs(B*t) > limit:
            continue
        for r in range(-limit, limit+1):
            if r and (-a*t) % r == 0 and abs((-a*t)//r) <= limit:
                out.add((B*t, r, (-a*t)//r))
    return out


def physical_exponents(eta, beta, omega, J):
    eta, beta, omega = map(F, (eta, beta, omega))
    r = s = F(3)
    h = ell = F(5,2)
    q = 3-eta
    outer = 1-r-s
    return (outer+h+ell+q-eta, outer+h+ell,
            outer+eta+3*q+beta-(J-1)*omega)


class PrimeIncidenceTests(unittest.TestCase):
    def test_constant_spectrum_is_retained_with_its_sign(self):
        self.assertEqual(prime_incidence_spectrum(5, 1, 1, 1, 1, 1), F(-25, 4))

    def test_resonance_keeps_B_and_a_in_different_coordinates(self):
        self.assertIn((3, 1, -2), resonance_pairs(2, 3, 4))
        self.assertNotIn((2, 1, -3), resonance_pairs(2, 3, 4))

    def test_outer_cost_and_all_frequency_tail_are_both_charged(self):
        self.assertEqual(physical_exponents(F(6,5), F(7,10), F(1,25), 48),
                         (F(3,5), F(0), F(21,50)))

    def test_composite_q_does_not_receive_prime_formula(self):
        with self.assertRaises(ValueError):
            prime_incidence_spectrum(6, 1, 1, 2, 2, 2)

    def test_prime_formula_matches_full_spectrum_including_zero_planes(self):
        checks = 0
        for q in (2,3,5,7,11):
            for a,B in ((1,1),(2,3),(3,4),(5,6)):
                if gcd(a*B,q) != 1:
                    continue
                for k,r,s in product(range(-3,4), repeat=3):
                    self.assertEqual(prime_incidence_spectrum(q,a,B,k,r,s),
                                     triple_spectrum(q,a*pow(B,-1,q),k,r,s))
                    checks += 1
        self.assertEqual(checks, 4459)

    def test_invalid_units_are_not_silently_inverted(self):
        for q,a,B in ((1,1,1),(5,5,1),(7,1,14),(15,1,1)):
            with self.assertRaises(ValueError):
                prime_incidence_spectrum(q,a,B,1,1,1)
        with self.assertRaises(ValueError):
            resonance_pairs(2,4,10)

    def test_composite_nonunit_counterexample_stays_outside_this_sector(self):
        self.assertEqual(triple_spectrum(6,1,2,2,2), F(-9,2))
        self.assertNotEqual(triple_spectrum(6,1,2,2,2), 0)

    def test_finite_inverse_transform_keeps_constant_and_normalization(self):
        for q,a,B in ((2,1,1),(3,1,2),(5,2,3)):
            direct, spectral = defaultdict(F), defaultdict(F)
            weights = {(z,x,y):F((z+x-y)*(1+z*x*y),1+z*z+x*x+y*y)
                       for z,x,y in product(range(1,q),repeat=3)}
            for (z,x,y),w in weights.items():
                direct[-a*pow(B*z,-1,q)*x*y % q] += w
                direct[0] += w*F(1,q-1)
            for k,r,s in product(range(1,q),repeat=3):
                coeff = F(int((a*k+B*r*s)%q==0),q)-F(1,q*(q-1))
                for (z,x,y),w in weights.items():
                    phase = (-k*z-r*x-s*y) % q
                    spectral[phase] += coeff*w
            self.assertTrue(roots_equal([(F(k,q),v) for k,v in direct.items()],
                                        [(F(k,q),v) for k,v in spectral.items()]))

    def test_literal_integer_resonance_has_exact_parameterization(self):
        checks = 0
        for a,B in product(range(1,17),repeat=2):
            if gcd(a,B) != 1:
                continue
            actual = {(k,r,s) for k,r,s in product(range(-12,13),repeat=3)
                      if k*r*s and a*k+B*r*s==0}
            self.assertEqual(actual, resonance_pairs(a,B,12))
            checks += 1
        self.assertEqual(checks, 159)

    def test_nonzero_congruence_is_not_an_integer_resonance(self):
        q,a,B,k,r,s = 101,2,3,49,1,1
        self.assertEqual(a*k+B*r*s, q)
        self.assertNotIn((k,r,s), resonance_pairs(a,B,50))
        self.assertNotEqual(prime_incidence_spectrum(q,a,B,k,r,s),0)

    def test_small_frequency_box_excludes_only_nonzero_q_multiples(self):
        q,a,B = 101,2,3
        self.assertLess(a*3+B*4*4,q)
        for k,r,s in product(range(-3,4),range(-4,5),range(-4,5)):
            if k*r*s and (a*k+B*r*s)%q==0:
                self.assertEqual(a*k+B*r*s,0)

    def test_subunit_frequency_scale_is_not_rounded_up(self):
        natural, inflation = F(1,100), F(2)
        actual = [k for k in (-1,1) if abs(k)<=natural*inflation]
        self.assertEqual(actual, [])
        self.assertNotEqual(actual, [-1,1])

    def test_nonzero_integer_ramanujan_floor_bound_includes_tiny_scales(self):
        checks = 0
        for q,L in product((2,3,5,7,11,101),[F(i,8) for i in range(1,193)]):
            top = int(2*L)
            ram = lambda n: q-1 if n%q==0 else -1
            self.assertLessEqual(sum(abs(ram(n)) for n in range(1,top+1)),4*L)
            self.assertLessEqual(sum(abs(ram(n)) for n in range(-top,top+1) if n),8*L)
            checks += 1
        self.assertEqual(checks,1152)

    def test_zero_label_would_invalidate_floor_budget(self):
        q,L = 101,F(1,100)
        self.assertGreater(q-1,8*L)

    def test_full_m_unit_mask_keeps_unsigned_square_quotient(self):
        labels = (-2,-1,1,2)
        for e,q in ((6,5),(10,7),(15,11)):
            direct, expanded = defaultdict(F), defaultdict(F)
            for b,c in product(range(2,7),repeat=2):
                B=b*c
                coeff=mobius(e)*mobius(q)*mobius(b)*mobius(c)
                if B>30 or gcd(B,e*q)!=1 or not coeff:
                    continue
                for n,x,y in product(range(20,51),labels,labels):
                    if n%B or gcd(x*y,q)!=1:
                        continue
                    w=F((n+e+x*y)**2,1+n*e)*coeff
                    if gcd(n,e*q)==1:
                        direct[-e*x*y*pow(n,-1,q)%q]+=w
                        direct[0]+=w*F(1,q-1)
                    for d in divisors(e):
                        if n%(B*d):
                            continue
                        z=n//(B*d)
                        if gcd(z,q)!=1:
                            continue
                        a=e//d
                        val=w*mobius(d)
                        expanded[-a*x*y*pow(B*z,-1,q)%q]+=val
                        expanded[0]+=val*F(1,q-1)
            self.assertTrue(all(direct[k]==expanded[k] for k in set(direct)|set(expanded)))
        # b=c is legal; m=4 is also legal when prime to e*q.
        self.assertEqual(gcd(2,2),2)
        self.assertEqual(gcd(4,5*7),1)
        self.assertEqual(mobius(4),0)

    def test_normalized_weight_has_no_a_or_B_derivative_multiplier(self):
        e,q,B,R,H,L = 30,101,49,3000,701,811
        for d in divisors(e):
            Z,X,Y = F(R,B*d),F(H,e),F(L,e)
            z,x,y = Z*F(3,2),X*F(-3,4),Y*F(5,4)
            self.assertEqual((F(B*d,R)*z,F(e,L)*y,F(e,H)*x),
                             (F(3,2),F(5,4),F(-3,4)))
            a=e//d
            self.assertEqual(a*F(q,Z),F(q*B*e,R))

    def test_all_frequency_tail_is_uniform_below_one(self):
        for L,scale,J in product((F(1,100),F(1,4),F(1),F(3),F(20)),(2,5),(4,8)):
            tail=sum(((1+F(n)/L)**(-J) for n in range(1,1001) if n>scale*L),F(0))*2
            self.assertLessEqual(tail,4*L*F(scale)**(1-J))

    def test_hyperbolic_pair_count_and_harmonic_cost_are_distinct(self):
        for limit in (1,4,12,35,100):
            pairs=[(b,c) for b in range(1,limit+1) for c in range(1,limit//b+1)]
            harmonic=sum((F(1,n) for n in range(1,limit+1)),F(0))
            self.assertLessEqual(len(pairs),limit*harmonic)
            self.assertLessEqual(sum((F(1,b*c) for b,c in pairs),F(0)),harmonic**2)

    def test_high_derivative_tail_cannot_be_paid_with_J_four(self):
        self.assertGreater(physical_exponents(F(6,5),F(7,10),F(1,25),4)[2],1)
        self.assertLess(physical_exponents(F(6,5),F(7,10),F(1,25),48)[2],F(3,5))

    def test_new_sector_has_both_long_factors_and_preserves_long_product_rest(self):
        U=V=3
        selected=[(b,c) for b,c in product(range(1,21),repeat=2) if b>U and c>V and b*c<=64]
        remaining=[(b,c) for b,c in product(range(1,21),repeat=2) if b>U and c>V and b*c>64]
        self.assertIn((5,7),selected)
        self.assertIn((11,13),remaining)
        self.assertNotIn((2,2),selected)
        self.assertEqual(set(selected)&set(remaining),set())

    def test_actual_physical_support_with_double_long_factors(self):
        e,q,b,c,Bmax,inflation = 1009,1000000007,5,7,64,2
        self.assertTrue(all(q%p for p in range(2,isqrt(q)+1)))
        S=R=e*q
        T=(8*S)**(1/3)
        H=L=S/sqrt(T)
        B=b*c
        m=ceil(R/B)
        while gcd(m,B*e*q)!=1 or mobius(m)==0:
            m+=1
        n=B*m
        u=v=ceil(H/e)
        cutoff=int(T**.1)
        self.assertTrue(b>cutoff and c>cutoff and B<=Bmax)
        self.assertTrue(R<=n<2*R)
        self.assertEqual(gcd(n,e*q),1)
        self.assertEqual(gcd(u*v,q),1)
        self.assertNotEqual(mobius(n),0)
        self.assertLessEqual(Bmax*inflation**2*(4*e*q/R+16*e*e*q*q/(H*L)),q/2)
        y=(3*sqrt(T)*n/4+e*v)/S
        self.assertTrue(sqrt(T)/2<=y<=2*sqrt(T))


if __name__ == '__main__':
    unittest.main()
