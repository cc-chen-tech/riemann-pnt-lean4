from fractions import Fraction as F
from math import gcd
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts import mwkf_mobius_type_identity as type_identity
from scripts.mwkf_mobius_type_identity import (
    bilinear_gauss_via_orthogonality,
    c_u,
    centered_completion_via_orthogonality,
    centered_product_frequency_coefficients,
    double_centered_completion_via_orthogonality,
    crt_reciprocity_numerators,
    double_split_mobius_identity,
    determinant_lattice_solution,
    mobius,
    poisson_congruence_reparametrization,
    split_mobius_identity,
    signed_shift_solutions,
    type_scale_bounds,
)
from scripts.audit_mwkf_coverage import (
    wright_denominator_factor_adapter,
    wright_type_i_adapter,
)
from scripts.audit_mwkf_ranges import boundary_witnesses


TYPE_NOTE = Path("docs/research/2026-08-24-mwkf-mobius-type-i-ii.md")


def test_truncated_divisor_coefficient() -> None:
    assert c_u(1, 3) == 1
    assert c_u(6, 3) == -1  # 1 + mu(2) + mu(3)
    assert c_u(12, 4) == -1  # divisors 1,2,3,4


def test_exact_mobius_type_split_for_all_small_integers() -> None:
    for cutoff in range(1, 9):
        for n in range(cutoff + 1, 80):
            lhs, type_i, type_ii = split_mobius_identity(
                n, cutoff_u=cutoff, cutoff_v=5
            )
            assert lhs == mobius(n)
            assert lhs == -(type_i + type_ii)


def test_exact_double_mobius_split_has_four_sectors() -> None:
    for cutoff in range(1, 6):
        for r in range(cutoff + 1, 30):
            for s in range(cutoff + 1, 30):
                lhs, sectors = double_split_mobius_identity(
                    r,
                    s,
                    cutoff_u=cutoff,
                    cutoff_v=4,
                )
                assert lhs == mobius(r) * mobius(s)
                assert lhs == sum(sectors.values())
                assert set(sectors) == {"I/I", "I/II", "II/I", "II/II"}


def test_full_truncated_mobius_convolution_vanishes_above_the_cutoff() -> None:
    """Catch localizing the s*a factorization before its exact centering."""
    adapter = getattr(
        type_identity,
        "full_truncated_mobius_convolution",
        None,
    )
    assert adapter is not None, "truncated Möbius convolution helper is missing"

    for cutoff in range(1, 9):
        for n in range(1, 80):
            expected = mobius(n) if n <= cutoff else 0
            assert adapter(n=n, cutoff_u=cutoff) == expected


def test_type_sector_convolution_extracts_negative_mobius_above_cutoff() -> None:
    """Catch forgetting the a>U restriction in the actual Type sector."""
    adapter = getattr(
        type_identity,
        "restricted_truncated_mobius_convolution",
        None,
    )
    assert adapter is not None, "restricted Möbius convolution helper is missing"

    for cutoff in range(1, 9):
        for n in range(1, 80):
            expected = -mobius(n) if n > cutoff else 0
            assert adapter(n=n, cutoff_u=cutoff) == expected


def test_two_general_zero_ray_sectors_move_mobius_to_primitive_slopes() -> None:
    """Catch claiming residual Möbius cancellation in the common k variable."""
    adapter = getattr(
        type_identity,
        "restricted_zero_ray_pair_convolution",
        None,
    )
    assert adapter is not None, "general zero-ray convolution helper is missing"

    for u, v, k, cutoff in (
        (1, 2, 3, 1),
        (2, 3, 5, 2),
        (2, 5, 3, 2),
        (3, 5, 2, 1),
    ):
        audit = adapter(u=u, v=v, k=k, cutoff_u=cutoff)
        assert audit.left_product == u * k
        assert audit.right_product == v * k
        assert audit.left_sector_sum == -mobius(u * k)
        assert audit.right_sector_sum == -mobius(v * k)
        assert audit.pair_sector_product == mobius(u) * mobius(v)
        assert audit.squarefree_ray_support
        assert audit.common_k_mobius_cancels_exactly

    shared_prime = adapter(u=2, v=3, k=10, cutoff_u=2)
    assert not shared_prime.squarefree_ray_support
    assert shared_prime.pair_sector_product == 0


def test_zero_ray_reciprocal_phase_only_sees_the_k_factorization() -> None:
    """Catch retaining a fake primitive-slope conductor after cancellation."""
    adapter = getattr(
        type_identity,
        "zero_ray_phase_reduction",
        None,
    )
    assert adapter is not None, "zero-ray phase reduction helper is missing"

    for g, s, a in ((13, 10, 21), (-13, 10, 21), (17, 6, 35)):
        audit = adapter(u=6, k=35, s=s, a=a, b=11, g=g)
        assert audit.s_u * audit.a_u == 6
        assert audit.s_k * audit.a_k == 35
        assert audit.original_fixed_phase == audit.reduced_fixed_phase
        assert audit.original_real_phase == audit.product_real_phase
        assert audit.original_common_b_phase == audit.product_common_b_phase
        assert audit.primitive_slope_removed_from_reciprocal_phase


def test_squarefree_factorization_gives_exact_common_b_phase() -> None:
    # e(n * bar(s)/(a*b)) splits into characters modulo a and b.
    for a, b, s, n in ((5, 6, 7, 11), (7, 10, 9, -13), (11, 14, 3, 17)):
        inverse, mod_a, mod_b = crt_reciprocity_numerators(
            s=s, a=a, b=b, n=n
        )
        assert (inverse - mod_a - mod_b).denominator == 1


def test_h_poisson_frequency_is_exact_shifted_equation() -> None:
    for r, s, delta, k in ((5, 7, 3, -2), (7, 11, -4, 3), (11, 13, 8, 0)):
        v, j = poisson_congruence_reparametrization(
            r=r, s=s, delta=delta, k=k
        )
        assert r * v - delta == j * s
        assert (r * v - delta) % s == 0


def test_global_determinant_lattice_keeps_all_v_j_solutions_coupled() -> None:
    for r, s, delta, k in (
        (5, 7, 3, -2),
        (7, 11, -4, 3),
        (11, 13, 8, 0),
    ):
        j, v = determinant_lattice_solution(
            r=r, s=s, delta=delta, translate=k
        )
        assert r * v - j * s == delta
        next_j, next_v = determinant_lattice_solution(
            r=r, s=s, delta=delta, translate=k + 1
        )
        assert next_j - j == r
        assert next_v - v == s


def test_zero_complementary_divisor_is_an_exact_proportionality_ray() -> None:
    """Catch reversing the two primitive ray coordinates in Delta=0."""
    adapter = getattr(
        type_identity,
        "proportional_diagonal_coordinates",
        None,
    )
    assert adapter is not None, "proportional-diagonal helper is missing"

    positive = adapter(n1=6, y1=14, n2=15, y2=35)
    assert positive.sign == 1
    assert positive.common_n_factor == 3
    assert positive.primitive_n1 == 2
    assert positive.primitive_n2 == 5
    assert positive.common_y_factor == 7
    assert 6 * 35 == 15 * 14
    assert 14 == positive.primitive_n1 * positive.common_y_factor
    assert 35 == positive.primitive_n2 * positive.common_y_factor

    negative = adapter(n1=-6, y1=14, n2=-15, y2=35)
    assert negative.sign == -1
    assert negative.common_n_factor == 3
    assert negative.primitive_n1 == 2
    assert negative.primitive_n2 == 5
    assert negative.common_y_factor == 7

    with pytest.raises(ValueError, match="not on the zero-complementary ray"):
        adapter(n1=6, y1=14, n2=15, y2=34)


def test_short_signed_shift_window_has_a_unique_j() -> None:
    assert signed_shift_solutions(
        r=101,
        s=103,
        v=10,
        delta_min=80,
        delta_max=90,
        sign=1,
    ) == ((9, 83),)
    assert signed_shift_solutions(
        r=101,
        s=103,
        v=10,
        delta_min=15,
        delta_max=25,
        sign=-1,
    ) == ((10, -20),)


def test_balanced_resonance_coordinates_have_only_five_fixed_slopes() -> None:
    """Catch a non-centered remainder convention or an omitted endpoint slope."""
    adapter = getattr(type_identity, "centered_resonance_coordinates", None)
    assert adapter is not None, "centered-resonance coordinates are missing"

    seen: set[int] = set()
    for r in range(10, 41):
        for s in range(10, 41):
            coordinates = adapter(r=r, s=s)
            assert r - s == coordinates.j * s + coordinates.w
            assert -s < 2 * coordinates.w <= s
            assert r == coordinates.linear_slope * s + coordinates.w
            assert coordinates.distance == abs(coordinates.w)
            assert -1 <= coordinates.j <= 3
            if gcd(r, s) == 1:
                assert gcd(s, coordinates.w) == 1
                for a in (-7, -1, 1, 5):
                    assert (a * r - a * coordinates.w) % s == 0
            seen.add(coordinates.j)
    assert seen == {-1, 0, 1, 2, 3}

    positive_tie = adapter(r=15, s=10)
    negative_tie = adapter(r=5, s=10)
    assert (positive_tie.j, positive_tie.w) == (0, 5)
    assert (negative_tie.j, negative_tie.w) == (-1, 5)


def test_coprime_centered_mobius_product_reindexes_through_qd() -> None:
    """Catch omitting (d,q)=1 or the d-restriction after gcd inversion."""
    adapter = getattr(
        type_identity,
        "coprime_centered_mobius_reindex",
        None,
    )
    assert adapter is not None, "coprime centered Möbius reindex is missing"

    for slope in (1, 2, 3, 4):
        for q in range(1, 8):
            for s in range(1, 24):
                for w in range(-9, 10):
                    r = slope * s + w
                    if r <= 0:
                        continue
                    direct = (
                        mobius(s)
                        * mobius(r)
                        * int(gcd(s, w) == 1)
                        * int(gcd(q, s * r) == 1)
                    )
                    assert adapter(
                        s=s,
                        w=w,
                        slope=slope,
                        q=q,
                    ) == direct


def test_signed_shift_helper_returns_every_solution_in_a_wide_window() -> None:
    assert signed_shift_solutions(
        r=5,
        s=7,
        v=8,
        delta_min=1,
        delta_max=15,
        sign=1,
    ) == ((4, 12), (5, 5))


def test_zero_v_has_no_solution_in_a_nonzero_submodular_shift_window() -> None:
    for sign in (-1, 1):
        assert signed_shift_solutions(
            r=101,
            s=103,
            v=0,
            delta_min=10,
            delta_max=20,
            sign=sign,
        ) == ()


def test_centered_nonzero_characters_recover_a_zero_at_origin_weight() -> None:
    values = (0, 3, -2, 5, 0, 7, -4)
    for residue, expected in enumerate(values):
        assert centered_completion_via_orthogonality(
            values, residue=residue
        ) == expected


def test_centered_completion_subtracts_the_origin_for_general_weights() -> None:
    values = (11, 3, -2, 5, 0)
    for residue, value in enumerate(values):
        assert centered_completion_via_orthogonality(
            values, residue=residue
        ) == value - values[0]


def test_centered_product_frequencies_group_without_loss() -> None:
    grouped = centered_product_frequency_coefficients(
        (
            (1, 2, F(3)),
            (2, 1, F(5)),
            (-1, -2, F(7)),
            (-2, 1, F(11)),
            (3, 0, F(101)),
        )
    )
    assert grouped == {2: F(15), -2: F(11)}


def test_centered_product_grouping_rejects_a_zero_completion_frequency() -> None:
    with pytest.raises(ValueError, match="completion frequency c"):
        centered_product_frequency_coefficients(((0, 3, F(1)),))


def test_bilinear_finite_gauss_kernel_has_the_exact_surviving_phase() -> None:
    coefficient, phase_residue = bilinear_gauss_via_orthogonality(
        r=5, modulus=13, c=4, v=7
    )
    assert coefficient == 13
    assert phase_residue == (5 * 4 * 7) % 13


def test_double_centering_recovers_a_weight_vanishing_on_both_axes() -> None:
    values = (
        (0, 0, 0, 0, 0),
        (0, 3, -2, 5, 7),
        (0, -4, 6, 1, 8),
        (0, 9, 2, -3, 4),
        (0, 5, -7, 6, 2),
    )
    for x, row in enumerate(values):
        for y, expected in enumerate(row):
            assert double_centered_completion_via_orthogonality(
                values, residue_x=x, residue_y=y
            ) == expected


def test_double_centering_is_inclusion_exclusion_for_general_weights() -> None:
    values = (
        (11, 2, 3),
        (5, 7, 13),
        (17, 19, 23),
    )
    assert double_centered_completion_via_orthogonality(
        values, residue_x=2, residue_y=1
    ) == F(19 - 17 - 2 + 11)


def test_one_third_split_has_exact_balanced_scales() -> None:
    scales = type_scale_bounds(F(3), u=F(1, 3), v=F(1, 3))
    assert scales.u_exp == F(1)
    assert scales.v_exp == F(1)
    assert scales.type_i_a_min == F(2)
    assert scales.type_ii_a_min == F(1)
    assert scales.type_ii_a_max == F(2)
    assert scales.type_ii_b_min == F(1)
    assert scales.type_ii_b_max == F(2)


def test_wright_type_i_fails_on_the_balanced_hard_endpoint() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    result = wright_type_i_adapter(
        box, a_factor=F(2), b_factor=F(1)
    )
    assert not result.applicable
    assert result.reason == "wright_hypotheses_fail"
    assert result.saving == F(-45, 8)


def test_wright_fixed_denominator_factor_still_loses_at_best_endpoint() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    result = wright_denominator_factor_adapter(
        box,
        fixed_factor=F(1),
        remaining_factor=F(2),
    )
    assert not result.applicable
    assert result.reason == "insufficient_saving"
    assert result.saving == F(-5)


def test_type_note_names_both_local_inequalities_and_blocker() -> None:
    text = TYPE_NOTE.read_text()
    for marker in (
        "## 2. Exact Möbius identity",
        "## 3. Reciprocity and exact Type-I/II sums",
        r"TI\(_{1/500}\)",
        r"TII\(_{1/500}\)",
        "## 4.1 Double Möbius split and denominator-factor audit",
        r"\mu^2(ab)=1",
        r"\frac{n_1\overline{s_1a_1}-n_2\overline{s_2a_2}}b",
        r"s_{\rm Wright,den}=-5",
        r"SP\(_b\)",
        "new spectral proposition status: unproved",
    ):
        assert marker in text
    assert "unconditional asymptotic proved" not in text
