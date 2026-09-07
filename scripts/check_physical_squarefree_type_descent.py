#!/usr/bin/env python3
"""Finite exact guards for the physical squarefree Type-descent note.

The large sieve, smooth-weight separation and asymptotic theorem are proved
on paper, not by these examples. No global zero-free conclusion is certified.
"""

from collections import Counter
from fractions import Fraction as F
from math import gcd
from pathlib import Path
import unittest

from check_physical_large_gcd_type_columns import (
    kernel, mobius, phi, product_terms, raw_column, root_normal_form, units,
)


def divisors(n):
    return [d for d in range(1, n+1) if n % d == 0]


def ramanujan(q, n):
    return sum(d*mobius(q//d) for d in divisors(gcd(q, n)))


def primitive_energy(q, coeff):
    return sum((a*b*ramanujan(q, n-m)
                for n, a in coeff.items() for m, b in coeff.items()
                if gcd(n, q) == gcd(m, q) == 1), F(0))


def ie_cauchy_majorant(q, coeff):
    # Exact primitive-frequency sum after Cauchy across f|q, before LS.
    result = F(0)
    for f in divisors(q):
        ell = q//f
        sub = {n//f: a for n, a in coeff.items() if n % f == 0}
        result += phi(f)*sum((a*b*ramanujan(ell, n-m)
                             for n, a in sub.items() for m, b in sub.items()), F(0))
    return len(divisors(q))*result


def descent_exponent(r, s, eta):
    q = s-eta
    return -eta+(q+r+max(r, 2*q))/2


class SquarefreeTypeDescentChecks(unittest.TestCase):
    def test_companion_markdown_has_no_embedded_controls(self):
        note = Path(__file__).resolve().parents[1] / "docs/research/2026-08-31-physical-squarefree-type-descent.md"
        bad = [(i, value) for i, value in enumerate(note.read_bytes())
               if (value < 32 and value not in (9, 10)) or value == 127]
        self.assertEqual(bad, [], "Markdown must not contain embedded ASCII controls")

    @staticmethod
    def coeff(length=17):
        return {n: F((-1)**n*(n % 4+1), n+2) for n in range(1, length+1)}

    def roots_equal(self, q, left, right):
        self.assertEqual(root_normal_form(q, left), root_normal_form(q, right))

    def test_full_unit_mask_inclusion_exclusion(self):
        a = self.coeff()
        for q in (1, 2, 6, 10, 15, 30):
            for k in units(q):
                direct = raw_column(q, k, a)
                expanded = [(-k*n, mobius(f)*c) for f in divisors(q)
                            for n, c in a.items() if n % f == 0]
                self.roots_equal(q, direct, expanded)

    def test_unit_lifts_have_phi_f_not_one(self):
        for q in (1, 6, 10, 15, 30, 42):
            for f in divisors(q):
                ell = q//f
                counts = Counter(k % ell for k in units(q))
                self.assertEqual(counts, Counter({t: phi(f) for t in units(ell)}))
                self.assertLessEqual(phi(f), f)
        self.assertEqual(phi(5), 4)

    def test_primitive_fractions_do_not_repeat(self):
        for M in (1, 8, 20):
            fractions = [F(t, ell) for ell in range(1, M+1) if mobius(ell)
                         for t in units(ell)]
            self.assertEqual(len(fractions), len(set(fractions)))
            fractions.sort()
            if len(fractions) > 1:
                gaps = [y-x for x, y in zip(fractions, fractions[1:])]
                gaps.append(1+fractions[0]-fractions[-1])
                self.assertGreaterEqual(min(gaps), F(1, M*M))

    def test_unrestricted_frequencies_would_repeat(self):
        self.assertEqual(F(2, 6), F(1, 3))
        self.assertNotIn(2, units(6))

    def test_exact_ie_cauchy_energy_majorant(self):
        for length in (1, 9, 19):
            a = self.coeff(length)
            for q in (1, 2, 6, 10, 15, 30):
                self.assertGreaterEqual(primitive_energy(q, a), 0)
                self.assertLessEqual(primitive_energy(q, a), ie_cauchy_majorant(q, a))

    def test_rescaled_length_and_lift_cost(self):
        X, M = F(31), F(20)
        for f in range(1, 21):
            self.assertEqual(f*(X/f+(M/f)**2), X+M*M/f)

    def test_divisor_weighted_energy_not_number_of_f(self):
        a = self.coeff(30)
        left = sum((c*c for f in range(1, 31) for n, c in a.items() if n % f == 0), F(0))
        right = sum((len(divisors(n))*c*c for n, c in a.items()), F(0))
        self.assertEqual(left, right)

    def test_empty_subsequence_endpoint(self):
        X = 9
        self.assertFalse([m for m in range(1, X//10+1)])
        self.assertEqual(units(1), [0])

    def test_centered_crt_descent_with_every_d(self):
        for q in (1, 2, 6, 10, 15, 30):
            for A in (1, 7):
                if gcd(A, q) != 1:
                    continue
                for k in range(q):
                    d, ell = gcd(k, q), q//gcd(k, q)
                    t = k//d
                    lowered = [(d*x, mobius(d)*c)
                               for x, c in kernel(ell, t, A*pow(d, -1, ell))]
                    self.roots_equal(q, kernel(q, k, A), lowered)

    def test_type_partition_is_exact_and_unique(self):
        for q in (1, 6, 10, 15, 30, 42):
            reconstructed = [d*t for d in divisors(q) for t in units(q//d)]
            self.assertEqual(sorted(reconstructed), list(range(q)))
            self.assertEqual(len(reconstructed), len(set(reconstructed)))

    def test_descent_inverse_cannot_be_removed(self):
        q, d, ell, t, A = 15, 5, 3, 1, 1
        wrong = [(d*x, mobius(d)*c) for x, c in kernel(ell, t, A)]
        self.assertNotEqual(root_normal_form(q, kernel(q, d*t, A)), root_normal_form(q, wrong))

    def test_full_centered_completion_reassembled_by_d(self):
        a = self.coeff(8)
        for q in (6, 10, 15, 30):
            actual = [(-pow(n, -1, q), c) for n, c in a.items() if gcd(n, q) == 1]
            reassembled = [(0, c*F(mobius(q), phi(q)))
                           for n, c in a.items() if gcd(n, q) == 1]
            for d in divisors(q):
                ell = q//d
                for t in units(ell):
                    lowered = [(d*x, c) for x, c in kernel(ell, t, pow(d, -1, ell))]
                    reassembled += product_terms(raw_column(q, d*t, a), lowered, F(mobius(d), d*ell))
            self.roots_equal(q, actual, reassembled)

    def test_outer_d_factor_cannot_be_dropped(self):
        d, ell = 5, 3
        self.assertEqual(F(1, d*ell), F(1, d)*F(1, ell))
        self.assertNotEqual(F(1, d*ell), F(1, ell))

    def test_squared_d_layer_cost_and_convergence_exponents(self):
        Q, R = F(20), F(31)
        for d in range(1, 21):
            self.assertEqual(F(1, d*d)*(Q/d)*R*(R+(Q/d)**2),
                             R*R*Q/d**3+R*Q**3/d**5)
        self.assertGreater(F(3, 2), 1)
        self.assertGreater(F(5, 2), 1)

    def test_actual_weight_scaling_has_no_d_growth(self):
        E, Q, S = F(100), F(31), F(3100)
        for e in (101, 137, 199):
            for d in (1, 2, 5, 17):
                self.assertEqual(e*d*(Q/d)/S, e*Q/S)
                self.assertLess(e*Q/S, 2)
        self.assertEqual(E*Q, S)

    def test_all_q_example_and_budget_boundary(self):
        eta = F(49, 20)
        bound = descent_exponent(F(3), F(3), eta)
        self.assertEqual(bound, F(33, 40))
        self.assertEqual(6-2*eta-bound, F(11, 40))
        self.assertEqual(1-bound, F(7, 40))
        self.assertEqual(descent_exponent(F(3), F(3), F(7, 3)), 1)
        self.assertGreater(descent_exponent(F(3), F(3), F(9, 4)), 1)

    def test_double_divisibility_is_not_all_genuine_gcd(self):
        s, h, delta = 30, 6, 5
        e = gcd(s, h*delta)
        self.assertEqual(e, 30)
        self.assertNotEqual(h % e, 0)
        self.assertNotEqual(delta % e, 0)


if __name__ == "__main__":
    unittest.main()
