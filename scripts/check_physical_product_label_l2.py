#!/usr/bin/env python3
"""Exact finite guards, not an asymptotic or zero-free certificate.

The companion mathematical note proves the product-label estimate for the
specified physical FP3 family. All masks, principal and crowded costs remain.
"""

from collections import defaultdict
from fractions import Fraction as F
from math import gcd
import unittest

from check_physical_large_gcd_type_columns import (
    kernel, mobius, phi, product_terms, raw_column, root_normal_form, units,
)
from check_common_frequency_parseval_conductor_average import square_terms
from check_physical_squarefree_type_descent import divisors, ramanujan


def label_products(b, c, d, ell):
    return [(u*v, x*y) for u, x in b.items() for v, y in c.items()
            if gcd(u*v, d*ell) == 1]


def label_kernel(ell, t, e, d, products):
    multiplier = e*pow(d, -1, ell)
    return [(z, w*a) for m, w in products
            for z, a in kernel(ell, t, multiplier*m)]


def exact_projected_energy(ell, e, d, products):
    multiplier = e*pow(d, -1, ell)
    W = sum((a for m, a in products), F(0))
    gram = sum((a*b*ramanujan(ell, multiplier*(m-n))
                for m, a in products for n, b in products), F(0))
    return (gram-W*W/phi(ell))/ell


def product_collision(ell, products):
    bins = defaultdict(F)
    for m, a in products:
        bins[m % ell] += a
    return sum((a*a for a in bins.values()), F(0))


def signed_labels(U):
    return [u for u in range(-int(2*U), int(2*U)+1) if u]


def balanced_costs(eta):
    q = 3-eta
    return {
        "first": -5+F(5, 2)+(q+3+max(F(3), 2*q))/2,
        "crowded": -eta+max(F(3), F(3, 2)+q),
        "principal": 3-eta,
        "counting": 6-2*eta,
    }


class ProductLabelL2Checks(unittest.TestCase):
    @staticmethod
    def labels():
        return ({-2: F(1, 2), -1: F(-2, 3), 1: F(1), 2: F(-1, 4)},
                {-3: F(2, 5), -1: F(-1), 1: F(3, 4), 3: F(1, 3)})

    def roots_equal(self, q, left, right):
        self.assertEqual(root_normal_form(q, left), root_normal_form(q, right))

    def test_unit_mean_uses_same_product_mask(self):
        b, c = self.labels()
        for ell in (2, 3, 5, 6, 10, 15):
            d, e = 7, 1
            products = label_products(b, c, d, ell)
            W = sum((a for m, a in products), F(0))
            actual = [(-e*m*pow(d, -1, ell)*pow(w, -1, ell), a)
                      for w in units(ell) for m, a in products]
            self.roots_equal(ell, actual, [(0, mobius(ell)*W)])

    def test_dropping_label_mask_changes_centering(self):
        b, c = {1: F(1), 2: F(1)}, {1: F(1)}
        actual = label_products(b, c, 2, 3)
        self.assertEqual(sum(a for m, a in actual), 1)
        self.assertEqual(sum(b.values())*sum(c.values()), 2)

    def test_complete_centered_product_parseval_exact(self):
        b, c = self.labels()
        for ell in (2, 3, 5, 6, 10, 15):
            for d in (1, 7):
                products = label_products(b, c, d, ell)
                terms = [(z, a/F(ell*ell)) for t in range(ell)
                         for z, a in square_terms(ell, label_kernel(ell, t, 1, d, products))]
                target = exact_projected_energy(ell, 1, d, products)
                self.roots_equal(ell, terms, [(0, target)])

    def test_projection_is_bounded_by_product_collision(self):
        b, c = self.labels()
        for ell in (1, 2, 3, 5, 6, 10, 15):
            products = label_products(b, c, 7, ell)
            value = exact_projected_energy(ell, 1, 7, products)
            self.assertGreaterEqual(value, 0)
            self.assertLessEqual(value, product_collision(ell, products))

    def test_unit_multiplier_only_permutes_collision_classes(self):
        b, c = self.labels()
        for ell in (3, 5, 6, 15):
            products = label_products(b, c, 7, ell)
            for multiplier in units(ell):
                moved = [(multiplier*m, a) for m, a in products]
                self.assertEqual(product_collision(ell, products), product_collision(ell, moved))

    def test_conductor_one_centered_kernel_is_zero(self):
        b, c = self.labels()
        products = label_products(b, c, 7, 1)
        self.roots_equal(1, label_kernel(1, 0, 1, 7, products), [])

    def test_product_representations_bounded_by_divisors(self):
        for U in (F(1, 2), F(1), F(2), F(3)):
            for V in (F(1, 2), F(3, 2), F(4)):
                counts = defaultdict(int)
                for u in signed_labels(U):
                    for v in signed_labels(V):
                        counts[u*v] += 1
                for m, r in counts.items():
                    self.assertLessEqual(r, 2*len(divisors(abs(m))))
                self.assertLessEqual(sum(counts.values()), 16*U*V)

    def test_finite_collision_bound_including_small_label_endpoints(self):
        for U in (F(1, 2), F(3, 4), F(1), F(3, 2), F(2), F(3)):
            for V in (F(1, 2), F(1), F(3, 2), F(2), F(4)):
                products = [(u*v, F(1)) for u in signed_labels(U) for v in signed_labels(V)]
                M = int(4*U*V)
                D = max(len(divisors(m)) for m in range(1, M+1))
                for ell in (1, 2, 3, 5, 6, 7, 10, 15):
                    self.assertLessEqual(product_collision(ell, products), 256*D*U*V*(1+U*V/ell))

    def test_empty_label_domain_is_zero(self):
        self.assertEqual(signed_labels(F(2, 5)), [])
        self.assertEqual(product_collision(3, []), 0)

    def test_integer_product_capacity_per_residue(self):
        for M in range(1, 18):
            for ell in (1, 2, 3, 7, 15):
                for j in range(ell):
                    count = sum(z % ell == j for z in range(-M, M+1) if z)
                    self.assertLessEqual(count, F(2*M, ell)+2)

    def test_product_type_descent_retains_every_label_mask(self):
        b, c = self.labels()
        for q in (6, 10, 15):
            products = label_products(b, c, 1, q)
            for k in range(q):
                d, ell = gcd(k, q), q//gcd(k, q)
                actual = [(z, w*a) for m, w in products for z, a in kernel(q, k, m)]
                smaller_products = label_products(b, c, d, ell)
                lowered = [(d*z, mobius(d)*a)
                           for z, a in label_kernel(ell, k//d, 1, d, smaller_products)]
                self.roots_equal(q, actual, lowered)

    def test_joint_scalar_with_principal_recovers_original(self):
        b, c = self.labels()
        a = {n: F(mobius(n), n+1) for n in range(1, 9)}
        for q in (3, 5, 6, 10):
            products = label_products(b, c, 1, q)
            beta = F(mobius(q), 2)
            actual = [(-m*pow(n, -1, q), beta*x*y)
                      for n, x in a.items() if gcd(n, q) == 1 for m, y in products]
            W = sum((y for m, y in products), F(0))
            full = [(0, beta*x*W*F(mobius(q), phi(q)))
                    for n, x in a.items() if gcd(n, q) == 1]
            for d in divisors(q):
                ell = q//d
                smaller_products = label_products(b, c, d, ell)
                for t in units(ell):
                    lowered = [(d*z, y) for z, y in label_kernel(ell, t, 1, d, smaller_products)]
                    full += product_terms(raw_column(q, d*t, a), lowered, beta*F(mobius(d), d*ell))
            self.roots_equal(q, actual, full)

    def test_four_squared_d_costs(self):
        R, Q, UV = F(31), F(20), F(7, 2)
        for d in range(1, 21):
            layer = R*(R+(Q/d)**2)*(Q/d)*UV*(1+UV*d/Q)/(d*d)
            four = R*R*Q*UV/d**3 + R*Q**3*UV/d**5 + R*R*UV*UV/d**2 + R*Q*Q*UV*UV/d**4
            self.assertEqual(layer, four)

    def test_crowded_sqrt_R_times_Q_not_sqrt_RQ(self):
        R, Q = F(9), F(4)
        self.assertEqual((3*Q)**2, R*Q*Q)
        self.assertNotEqual(R*Q*Q, R*Q)

    def test_e_label_reassembly_costs(self):
        for E in range(1, 30):
            self.assertLessEqual(sum((F(1, e) for e in range(E+1, 2*E+1)), F(0)), 1)
            self.assertLessEqual(sum((F(1, e*e) for e in range(E+1, 2*E+1)), F(0)), F(1, E))

    def test_exact_physical_example(self):
        cost = balanced_costs(F(9, 4))
        self.assertEqual(cost, {"first": F(7, 8), "crowded": F(3, 4),
                                "principal": F(3, 4), "counting": F(3, 2)})
        self.assertEqual(cost["counting"]-max(cost["first"], cost["crowded"]), F(5, 8))

    def test_threshold_and_uncovered_principal_are_not_hidden(self):
        cost = balanced_costs(F(2))
        self.assertEqual(max(cost["first"], cost["crowded"]), 1)
        cost = balanced_costs(F(19, 10))
        self.assertEqual(max(cost["first"], cost["crowded"]), F(11, 10))
        self.assertEqual(cost["principal"], F(11, 10))

    def test_actual_four_variable_rescaling_uniform_in_d(self):
        e, Q, S = F(137), F(31), F(3100)
        for d in (1, 2, 5, 17):
            self.assertEqual(e*d*(Q/d)/S, e*Q/S)

    def test_nonempty_bertrand_exponent_geometry(self):
        e, q = F(9), F(3)
        t = (e+q)/3
        label = e+q-t/2-e
        self.assertEqual(t, 4)
        self.assertEqual(e/t, F(9, 4))
        self.assertEqual(label, 1)
        self.assertLess(label, q)


if __name__ == "__main__":
    unittest.main()
