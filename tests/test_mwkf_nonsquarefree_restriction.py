"""Finite regressions for the restored nonsquarefree residual, not upper bounds."""
import sys
import unittest
from fractions import Fraction as F
from math import gcd, isqrt
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.audit_mobius_type_ii import (
    mobius_two_cutoff_centered_divisor_split as split,
    squarefree_high_product_multiplicity,
)
from scripts.mwkf_mobius_type_identity import divisors, mobius


class NonsquarefreeRestrictionTests(unittest.TestCase):
    def test_actual_type_coefficient_has_nonzero_omitted_term(self):
        row = split(4, product_cutoff=4, cutoff_left=2, cutoff_right=2)
        self.assertEqual((row.density, row.centered, row.complementary),
                         (F(-1, 4), F(1, 4), F(0)))
        self.assertEqual(row.total, 0)
        self.assertNotEqual(row.density + row.complementary, 0)

    def test_mixed_support_restores_remainder_with_minus_sign(self):
        rows = {n: split(n, product_cutoff=4, cutoff_left=2, cutoff_right=2)
                for n in (4, 6)}
        full = sum(r.density + r.complementary for r in rows.values())
        sf = rows[6].density + rows[6].complementary
        remainder = -rows[4].centered
        self.assertEqual((full, sf, remainder), (F(-1, 2), F(-1, 4), F(-1, 4)))
        self.assertEqual(full, sf + remainder)
        self.assertNotEqual(full, sf - remainder)

    def test_signed_weighted_reassembly_keeps_all_n(self):
        for u, v, cutoff in ((1, 1, 1), (2, 2, 4), (2, 3, 9), (4, 2, 16)):
            for mode in (0, 1):
                full = sf = remainder = F(0)
                for n in range(max(u, v) + 1, 81):
                    weight = F((n * n + (mode + 1) * n) % 13 - 6, n + 1)
                    row = split(n, product_cutoff=cutoff, cutoff_left=u, cutoff_right=v)
                    full += weight * (row.density + row.complementary)
                    if mobius(n):
                        sf += weight * (row.density + row.complementary)
                    else:
                        remainder -= weight * row.centered
                self.assertEqual(full, sf + remainder)

    def test_original_style_shifted_mobius_weights_do_not_change_identity(self):
        full = sf = remainder = F(0)
        for s in range(17, 33):
            for d in range(1, 9):
                if gcd(s, d) != 1:
                    continue
                n = s + d
                weight = F(mobius(s) * (d * d - 3 * d + 1), 1 + s)
                row = split(n, product_cutoff=9, cutoff_left=3, cutoff_right=3)
                full += weight * (row.density + row.complementary)
                if mobius(n):
                    sf += weight * (row.density + row.complementary)
                else:
                    remainder -= weight * row.centered
        self.assertNotEqual(remainder, 0)
        self.assertEqual(full, sf + remainder)

    def test_squarefree_bilinear_switch_remains_exact_on_its_own_support(self):
        for n in range(5, 101):
            if not mobius(n):
                continue
            row = split(n, product_cutoff=4, cutoff_left=2, cutoff_right=2)
            switched = sum(
                mobius(n // m) * mobius(n)
                * squarefree_high_product_multiplicity(m, cutoff_left=2, cutoff_right=2)
                for m in divisors(n) if m > 4
            )
            self.assertEqual(switched, row.complementary)

    def test_boundary_is_not_silently_included_in_the_pointwise_identity(self):
        for n in (1, 2):
            with self.assertRaises(ValueError):
                split(n, product_cutoff=4, cutoff_left=2, cutoff_right=2)

    def test_unmasked_zero_sum_does_not_bound_a_restricted_subsum(self):
        centered = [F(1 if n % 2 == 0 else -1, 2) for n in range(1, 9)]
        self.assertEqual(sum(centered), 0)
        self.assertEqual(sum(x * (1 - mobius(n) ** 2)
                             for n, x in enumerate(centered, 1)), 1)

    def test_simple_square_divisibility_mask_has_exact_linear_bias(self):
        for blocks in range(1, 65):
            full = sum(F(1 if n % 2 == 0 else -1, 2)
                       for n in range(1, 4 * blocks + 1))
            masked = sum(F(1, 2) for n in range(1, 4 * blocks + 1) if n % 4 == 0)
            self.assertEqual(full, 0)
            self.assertEqual(masked, F(blocks, 2))

    def test_shift_coprimality_does_not_remove_the_mask_bias(self):
        self.assertTrue(all(gcd(101, d) == 1 for d in range(17, 33)))
        full = sum(F(1 if (101 + d) % 2 == 0 else -1, 2) for d in range(17, 33))
        masked = sum(F(1 if (101 + d) % 2 == 0 else -1, 2)
                     * (1 - mobius(101 + d) ** 2) for d in range(17, 33))
        self.assertEqual((full, masked), (0, F(3, 2)))

    def test_complete_nonsquarefree_mask_keeps_all_square_divisors(self):
        for n in range(1, 601):
            reconstructed = -sum(mobius(j) for j in range(2, isqrt(n) + 1)
                                 if n % (j * j) == 0)
            self.assertEqual(reconstructed, 1 - mobius(n) ** 2)
        # 36 is counted through both 4 and 9, with 36 restoring overlap.
        self.assertEqual((-mobius(2), -mobius(3), -mobius(6)), (1, 1, -1))

    def test_mu_not_mu_squared_is_not_a_nonsquarefree_indicator(self):
        self.assertEqual(1 - mobius(3) ** 2, 0)
        self.assertEqual(1 - mobius(3), 2)

    def test_general_arithmetic_mask_changes_the_complete_period_mean(self):
        # The period-4 mean is 1/8, not the unrestricted mean zero.
        kernel = {n: F(1 if n % 2 == 0 else -1, 2) for n in range(4)}
        self.assertEqual(sum(kernel.values()) / 4, 0)
        self.assertEqual(sum(value for n, value in kernel.items() if n % 4 == 0) / 4,
                         F(1, 8))


if __name__ == "__main__":
    unittest.main()
