#!/usr/bin/env python3
"""Finite guards for principal-tail normalization; NOT analytic tail proofs.

Run with Python 3, standard library only.  The paper supplies integration,
stationary phase and infinite-sum arguments; these checks cannot certify them.
"""

from fractions import Fraction as F
from itertools import product
from math import gcd
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.audit_mobius_type_ii import ramanujan_sum
from scripts.mwkf_mobius_type_identity import divisors, mobius


def packet_cost(*, T, q, R, S, M, K, W, C):
    """Raw row-count times row-majorant, without the top-face substitution."""
    T, q, R, S, M, K, W, C = map(F, (T, q, R, S, M, K, W, C))
    u_length, n_length = S/(W*C), M/(W*C)
    rows = R*u_length*W*C*n_length
    single_row = T/(q*u_length*S*C*K)
    return rows*single_row


class PrincipalTailGuards(unittest.TestCase):
    def test_n_length_below_top_face_is_not_dropped(self):
        # U=15, n-length=11, 660 rows, per-row cost=5/66.
        self.assertEqual(packet_cost(T=100, q=1, R=2, S=30,
                                     M=22, K=F(22, 15), W=1, C=2), F(50))

    def test_top_face_does_not_remove_outer_q_or_c(self):
        # K=MR/S; the final answer is T/(q C), not T or T/q.
        self.assertEqual(packet_cost(T=144, q=3, R=5, S=210,
                                     M=35, K=F(5, 6), W=5, C=7), F(48, 7))

    def test_all_dyadic_n_lengths_keep_the_same_normalized_budget(self):
        # Mutation n_length=1 fails for every M>WC.
        for W, C, u, n, R, q in product((1, 2), (1, 3), (1, 5),
                                       (1, 2, 16), (1, 7), (1, 2)):
            S, M = u*W*C, n*W*C
            self.assertEqual(packet_cost(T=64, q=q, R=R, S=S, M=M,
                                         K=F(M*R, S), W=W, C=C), F(64, q*C))

    def test_exact_squared_saddle_coefficient_restores_one_over_u(self):
        for q, r, u, w, c in product((1, 2, 5), repeat=5):
            s = u*w*c
            phi = sum(gcd(j, s) == 1 for j in range(s))
            # Square PT4/u before multiplying the saddle square.
            lhs = F(4*w*w, q*q*phi*phi*r*s*u*u)*F(u*c*r, w)
            self.assertEqual(lhs, F(4, q*q*u*u*phi*phi))

    def test_deleted_origin_divisor_sum_with_inherited_squarefree_parent(self):
        for s in range(1, 101):
            if mobius(s):
                phi = sum(gcd(j, s) == 1 for j in range(s))
                self.assertEqual(sum(w*mobius(w) for w in divisors(s)),
                                 mobius(s)*phi)

    def test_squarefree_parent_cannot_be_recovered_from_mu_u_mu_w(self):
        # (u,w,c)=(1,1,4) survives displayed mu_u*mu_w but is not physical.
        self.assertEqual(mobius(1)*mobius(1), 1)
        self.assertEqual(mobius(4), 0)
        self.assertEqual(sum(w*mobius(w) for w in divisors(4)), -1)

    def test_squareful_original_gcd_has_zero_original_coefficient(self):
        for q, r, s in ((4, 3, 5), (9, 2, 7), (12, 5, 7)):
            self.assertEqual(mobius(q*r)*mobius(q*s), 0)
            self.assertNotEqual(mobius(r)*mobius(s), 0)

    def test_positive_rational_lattice_has_gap_and_keeps_both_x_signs(self):
        signs = set()
        for u, c, n, r in product((1, 2, 5), repeat=4):
            for j in range(1, 11):
                x = j-n*c*r
                if x and gcd(x, u) == 1:
                    y = F(n*c*r+x, u*c)
                    self.assertGreaterEqual(y, F(1, u*c))
                    signs.add(x > 0)
        self.assertEqual(signs, {False, True})

    def test_small_k_support_really_empty_even_at_lattice_endpoint(self):
        T, N = 2, 8
        K = F(1, T**8)
        for u, c in product(range(1, N+1), repeat=2):
            if u*c <= N:
                self.assertLess(2*K, F(1, u*c))
        # The equality endpoint cannot be thrown away at K=1/(2uc).
        self.assertEqual(2*F(1, 2*6), F(1, 6))

    def test_empty_lattice_does_not_delete_the_signed_nonzero_spectrum(self):
        # Finite periodic analogue f(x)=1-cos(2*pi*x): all integer
        # samples vanish but coefficients at k=0,+u,-u are 1,-1/2,-1/2.
        # This is an exact guard, NOT a test of Schwartz Poisson tails.
        for u in (1, 2, 3, 6, 10, 30):
            phi = sum(gcd(j, u) == 1 for j in range(u))
            nonzero = -F(ramanujan_sum(u, u)+ramanujan_sum(u, -u), 2)
            self.assertEqual(nonzero, -phi)
            self.assertNotEqual(nonzero, 0)
            self.assertEqual(ramanujan_sum(u, 0)+nonzero, 0)

    def test_only_modulus_one_has_a_deleted_unit_origin(self):
        self.assertEqual([u for u in range(1, 101) if gcd(0, u) == 1], [1])

    def test_ramanujan_partial_sums_pay_length_not_length_plus_one(self):
        for u in (1, 2, 6, 12, 30, 35):
            for X in (F(1, 8), F(1, 2), F(1), F(3, 2), F(11, 2), F(20)):
                total = sum(abs(ramanujan_sum(u, k)) for k in range(1, int(X)+1))
                self.assertLessEqual(total, len(divisors(u))*X)

    def test_weighted_ramanujan_guard_includes_dual_length_below_one(self):
        for u in (1, 3, 6, 30):
            for X in (F(1, 16), F(1, 2), F(1), F(3), F(12)):
                total = sum(F(abs(ramanujan_sum(u, k)), 1)/(1+F(k)/X)**2
                            for k in range(1, 129))
                self.assertLessEqual(total, len(divisors(u))*X)

    def test_small_k_square_root_tail_is_geometric_not_logarithmic(self):
        # Every other dyadic scale K_j=2^(-16-2j); sqrt(K_j)=2^(-8-j).
        for stop in (1, 2, 8, 64):
            total = sum(F(1, 2**(8+j)) for j in range(stop))
            self.assertLess(total, F(1, 128))

    def test_large_m_rational_gap_gives_four_powers_not_seven(self):
        # At maximal uc=N, y=1/N and m=T^8: my/T=T^4.
        T, u, w, c, n, j = 2, 2, 1, 4, 64, 1
        m = n*w*c
        self.assertEqual(u*c, T**3)
        self.assertEqual(m, T**8)
        self.assertEqual(F(m*j, u*c*T), T**4)

    def test_general_row_count_uses_nonempty_half_length_endpoint(self):
        # Nonempty [Z/2,2Z] can occur for Z=1/2, so no Z>=1 claim.
        for Z in (F(1, 2), F(3, 4), F(1), F(3, 2), F(9, 2)):
            count = sum(Z/2 <= k <= 2*Z for k in range(1, 11))
            self.assertLessEqual(count, 4*Z)
        self.assertTrue(F(1, 4) <= 1 <= 1)

    def test_local_centering_is_literal_global_ramanujan_restriction(self):
        # Wrongly using a zero additive mode or a mu(e)^2 factor fails.
        for s in range(1, 61):
            if not mobius(s):
                continue
            phi_s = sum(gcd(j, s) == 1 for j in range(s))
            for h, delta in product(range(-5, 6), repeat=2):
                if not h*delta:
                    continue
                q = s//gcd(s, h*delta)
                phi_q = sum(gcd(j, q) == 1 for j in range(q))
                self.assertEqual(F(ramanujan_sum(s, h*delta), phi_s),
                                 F(mobius(q), phi_q))


if __name__ == "__main__":
    unittest.main()
