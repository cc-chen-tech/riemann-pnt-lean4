#!/usr/bin/env python3
"""Finite PL1--PL11 guards; not proofs of PV, large sieve, or zero exclusion."""

import cmath
from fractions import Fraction as F
from itertools import product
from math import gcd, pi
from pathlib import Path
import unittest

from check_physical_centered_conductor_split import characters, roots_equal
from check_physical_large_gcd_type_columns import mobius, phi
from check_physical_squarefree_type_descent import divisors


def exponents(eta, z=None):
    eta = F(eta)
    z = F(5, 2)-F(3, 4)*eta if z is None else F(z)
    return {
        "high": 3-eta-z/2,
        "high_mixed1": 2-eta,
        "high_mixed2": 3-F(3, 2)*eta,
        "high_last": F(7, 2)-2*eta,
        "low_main": eta-2+z/2,
        "low_mixed1": -2+eta/2+F(3, 2)*z,
        "low_mixed2": eta-F(7, 2)+F(3, 2)*z,
        "low_last": -F(7, 2)+eta/2+F(5, 2)*z,
    }


def common_column(length, f, c, q0):
    """No ell argument: the unit mask belongs to the fixed coefficient column."""
    return {n: F(mobius(n)*(2*n-length), 3*length+1)
            for n in range(1, length+1) if gcd(n, f*c*q0) == 1}


def character_sum(column, phases, ell, conjugate=False):
    sign = -1 if conjugate else 1
    return sum(float(a)*cmath.exp(sign*2j*pi*float(phases[n % ell]))
               for n, a in column.items() if gcd(n, ell) == 1)


class CenteredPVLargeSieveChecks(unittest.TestCase):
    def test_gauss_times_two_pv_has_exact_ls_weight(self):
        for c, ell in product((1, 2, 3, 5, 7), (3, 5, 7, 15)):
            if gcd(c, ell) > 1:
                continue
            # Squared Gauss weight times squared ell from two PV bounds.
            left = F(ell**3, phi(c)**2*phi(ell)**2)
            right = F(ell, phi(c)**2)*F(ell, phi(ell))**2
            self.assertEqual(left, right)

    def test_induced_columns_keep_fixed_c_unit_mask_exact(self):
        for q in (6, 10, 15, 21, 30, 35):
            for ell, ambient in characters(q):
                if ell == 1:
                    continue
                c = q//ell
                small = {n % ell: z for n, z in ambient.items()}
                for f, q0 in ((1, 1), (11, 13)):
                    column = common_column(19, f, c, q0)
                    actual = [
                        (ambient[n % q], F(mobius(n)*(2*n-19), 58))
                        for n in range(1, 20) if gcd(n, f*q0*q) == 1
                    ]
                    reduced = [(small[n % ell], a) for n, a in column.items()
                               if gcd(n, ell) == 1]
                    self.assertTrue(roots_equal(actual, reduced), (q, ell, f))
                    self.assertTrue(roots_equal(
                        [(-z, a) for z, a in actual],
                        [(-z, a) for z, a in reduced]))

    def test_c_mask_cannot_be_omitted(self):
        self.assertNotIn(2, common_column(9, 1, 2, 1))
        self.assertIn(2, common_column(9, 1, 1, 1))
        self.assertFalse(roots_equal(
            [(F(1, 2), common_column(9, 1, 1, 1)[2])], []))

    def test_weighted_cauchy_exact_quadratic_character_columns(self):
        for f, c in product((1, 3), (1, 2, 5)):
            aa, bb = common_column(13, f, c, 1), common_column(19, f, c, 1)
            rows = []
            for ell in (3, 5, 7, 11):
                if gcd(ell, f*c) > 1:
                    continue
                _, phases = next((d, z) for d, z in characters(ell)
                                 if d == ell and set(z.values()) == {F(0), F(1, 2)})
                ch = lambda n: (0 if gcd(n, ell) > 1 else
                                (1 if phases[n % ell] == 0 else -1))
                av = sum(a*ch(n) for n, a in aa.items())
                bv = sum(b*ch(n) for n, b in bb.items())
                uv = sum(F(u, 13)*ch(u) for u in range(-5, 6)
                         if u and gcd(u, c) == 1)
                vv = sum(F(v+2, 17)*ch(v) for v in range(-6, 7)
                         if v and gcd(v, c) == 1)
                rows.append((F(ell, phi(ell)), av, bv, uv*vv, ch(c)))
            bound = max(abs(t) for _, _, _, t, _ in rows)
            lhs = sum(w*a*b*t*phase for w, a, b, t, phase in rows)
            ea = sum(w*a*a for w, a, _, _, _ in rows)
            eb = sum(w*b*b for w, _, b, _, _ in rows)
            self.assertLessEqual(lhs*lhs, bound*bound*ea*eb)

    def test_primitive_large_sieve_finite_numeric_fixtures(self):
        # Floating finite checks, explicitly NOT an analytic proof.
        for M, X, f, c in product((7, 15), (9, 21), (1, 3), (1, 2, 5)):
            column = common_column(X, f, c, 7)
            norm = sum(a*a for a in column.values())
            for conjugate in (False, True):
                energy = 0.0
                for ell in range(2, M+1):
                    if not mobius(ell) or gcd(ell, f*c*7) > 1:
                        continue
                    for conductor, phases in characters(ell):
                        if conductor == ell:
                            value = character_sum(column, phases, ell, conjugate)
                            energy += ell/phi(ell)*abs(value)**2
                cap = float((M*M+X-1)*norm)
                self.assertLessEqual(energy, cap+1e-9*max(1, cap))

    def test_low_full_square_without_length_restriction(self):
        for A, B, L in product((F(1, 2), F(1), F(3), F(17)), repeat=3):
            full = L*A*B*(A+L*L)*(B+L*L)
            pieces = L*(A*B)**2+L**3*(A*A*B+A*B*B)+L**5*A*B
            self.assertEqual(full, pieces)
            self.assertGreater(full, L*(A*B)**2)

    def test_cofactor_totient_divisor_budget_exact(self):
        for C in (F(1, 2), F(1), F(3, 2), F(4), F(13), F(50)):
            ns = [n for n in range(1, int(2*C)+1) if C <= n < 2*C]
            D = max((len(divisors(n)) for n in range(1, int(2*C)+1)), default=1)
            actual = sum(F(len(divisors(n))**2, phi(n)) for n in ns)
            reciprocal = sum(F(1, n) for n in ns)
            self.assertLessEqual(actual, D**3*reciprocal)
            self.assertLessEqual(reciprocal, 2)

    def test_all_f_powers_in_low_terms_exact_squares(self):
        E, R, Z = F(19), F(101), F(7)
        for f in range(1, 39):
            A, B = E/f, R/f
            self.assertEqual(Z*(A*B)**2, Z*(E*R)**2/f**4)
            self.assertEqual(Z**3*A*B*B, Z**3*E*R*R/f**3)
            self.assertEqual(Z**3*A*A*B, Z**3*E*E*R/f**3)
            self.assertEqual(Z**5*A*B, Z**5*E*R/f**2)

    def test_last_f_sum_is_harmonic_not_convergent(self):
        sums = [sum(F(1, f) for f in range(1, n+1)) for n in (2, 8, 32, 128)]
        self.assertEqual(sums, sorted(sums))
        self.assertGreater(sums[-1], 4)

    def test_balanced_exponents_match_all_eight_terms(self):
        for eta in (F(4, 3), F(7, 5), F(10, 7), F(3, 2), F(7, 4), F(2)):
            es = exponents(eta)
            expected = (
                F(7, 4)-F(5, 8)*eta, 2-eta, 3-F(3, 2)*eta,
                F(7, 2)-2*eta, F(5, 8)*eta-F(3, 4),
                F(7, 4)-F(5, 8)*eta, F(1, 4)-eta/8,
                F(11, 4)-F(11, 8)*eta,
            )
            self.assertEqual(tuple(es.values()), expected)
            z = F(5, 2)-F(3, 4)*eta
            self.assertTrue(0 <= z <= 3-eta)

    def test_envelope_and_sample_values(self):
        for eta in (F(4, 3), F(7, 5), F(10, 7), F(3, 2), F(7, 4), F(2)):
            upper = max(3-F(3, 2)*eta, F(7, 4)-F(5, 8)*eta)
            self.assertEqual(max(exponents(eta).values()), upper)
            self.assertLessEqual(upper, 1)
        self.assertEqual([max(exponents(x).values())
                          for x in (F(4, 3), F(7, 5), F(3, 2), F(2))],
                         [1, F(9, 10), F(13, 16), F(1, 2)])

    def test_below_boundary_old_high_cost_and_principal_remain(self):
        self.assertGreater(exponents(F(13, 10))["high_mixed2"], 1)
        self.assertEqual(3-F(7, 5), F(8, 5))
        self.assertGreater(3-F(7, 5), max(exponents(F(7, 5)).values()))

    def test_top_conductor_endpoint_is_not_Q(self):
        Q = 5
        self.assertTrue(Q < 7 <= 2*Q)
        self.assertTrue(any(d == 7 for d, _ in characters(7)))

    def test_full_pv_three_halves_exponent_endpoint(self):
        eta, q = F(3, 2), F(3, 2)
        low = exponents(eta, q)
        self.assertEqual(max(low[k] for k in low if k.startswith("low")), 1)

    def test_real_support_scaling_and_sobolev_budget(self):
        e, q, T = F(14), F(16), F(10)
        S = e+q
        H = S-T/2
        self.assertEqual((e/T, H-e), (F(7, 5), 11))
        self.assertLess(H-e, q)
        self.assertEqual(2*H, 2*S-T)
        self.assertTrue(2*6-4 > 5)
        self.assertFalse(6-2 > 5)

    def test_no_hidden_control_bytes(self):
        root = Path(__file__).resolve().parents[1]
        for path in (Path(__file__),
                     root/"docs/research/2026-08-31-physical-centered-pv-large-sieve.md"):
            self.assertEqual([(i, x) for i, x in enumerate(path.read_bytes())
                              if (x < 32 and x not in (9, 10)) or x == 127], [])


if __name__ == "__main__":
    unittest.main()
