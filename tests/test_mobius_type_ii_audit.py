from fractions import Fraction as F
from math import gcd
import sys
from pathlib import Path


sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.audit_mobius_type_ii import (
    MQWBlockSavings,
    PascadiFullResidueSavings,
    WrightFactorSavings,
    balanced_dual_low_mode_mobius_exponent,
    balanced_principal_character_mobius_exponent,
    c_coefficient,
    centered_dual_scales,
    centered_dual_common_mobius_exponent,
    character_large_sieve_unit_gap,
    coprime_indicator_via_mobius,
    dispersion_pointwise_mean_square_gap,
    dispersion_random_benchmark_gap,
    direct_fourfold_random_margin,
    elementary_large_sieve_loss,
    global_unit_principal_completion_margin,
    induced_gauss_outer_mobius_sign,
    inverse_product_phase_mod_one,
    mqw_block_savings,
    mqw_initial_rectangle_supremal_saving,
    mqw_initial_rectangle_witness,
    mobius_geometric_value,
    nonunit_principal_long_factor_floor,
    nonunit_principal_equal_mobius_exponent,
    nonunit_principal_h_boundary_slack,
    nonunit_principal_is_residual_face,
    nonunit_principal_trivial_loss,
    pascadi_balanced_gap,
    pascadi_2024_direct_dispersion_gap,
    pascadi_full_residue_savings,
    pascadi_optimal_delta,
    reduce_inverse_product_phase,
    ramanujan_sum,
    reverse_unit_affine_progression_length,
    reverse_unit_solution_count_gap,
    squarefree_outer_mobius_ramanujan,
    two_sided_mobius_geometric_value,
    wright_factor_covers,
    wright_factor_savings,
    wright_unbalanced_modulus_margin,
)
from scripts.audit_mwkf_ranges import boundary_witnesses


def naive_mobius(n: int) -> int:
    value = 1
    prime = 2
    remaining = n
    while prime * prime <= remaining:
        if remaining % prime == 0:
            remaining //= prime
            value = -value
            if remaining % prime == 0:
                return 0
            while remaining % prime == 0:
                remaining //= prime
        prime += 1
    if remaining > 1:
        value = -value
    return value


def least_depth(cutoff: int, limit: int) -> int:
    depth = 1
    power = cutoff
    while power < limit:
        depth += 1
        power *= cutoff
    return depth


def test_finite_mobius_geometric_identity_through_cutoff_power() -> None:
    limit = 200
    for cutoff in (2, 3, 5):
        depth = least_depth(cutoff, limit)
        for n in range(1, limit + 1):
            assert mobius_geometric_value(n, cutoff, depth) == naive_mobius(n)


def test_c_coefficient_has_the_required_initial_support_gap() -> None:
    for cutoff in (2, 3, 5, 11):
        assert [c_coefficient(n, cutoff) for n in range(1, cutoff + 1)] == [
            0
        ] * cutoff


def test_balanced_wright_factor_savings_are_literal_fractions() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert wright_factor_savings(box, F(0)) == WrightFactorSavings(
        first=F(-37, 8),
        second=F(-37, 8),
        third=F(-23, 5),
        fourth=F(-41, 10),
        fifth=F(-37, 8),
    )
    assert wright_factor_savings(box, F(1)) == WrightFactorSavings(
        first=F(-5),
        second=F(-39, 8),
        third=F(-97, 20),
        fourth=F(-21, 5),
        fifth=F(-9, 2),
    )


def test_balanced_box_is_uncovered_for_every_allowed_half_step_factor() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    for tau in (F(0), F(1, 2), F(1), F(3, 2)):
        assert not wright_factor_covers(box, tau)


def test_fixed_factor_never_improves_the_decisive_first_term() -> None:
    for box in boundary_witnesses().values():
        baseline = box.sigma / 8 - box.third_length
        for tau in (F(0), F(1, 4), F(1, 2), F(1)):
            savings = wright_factor_savings(box, tau)
            assert savings.first <= baseline


def test_pascadi_full_residue_optimum_is_the_exact_intersection() -> None:
    delta = pascadi_optimal_delta()
    assert delta == F(7, 191)
    savings = pascadi_full_residue_savings(delta)
    assert savings == PascadiFullResidueSavings(
        first=F(33, 191),
        second=F(33, 191),
        third=F(257, 764),
        fourth=F(13, 24),
    )
    assert min(savings.values()) == F(33, 191)


def test_pascadi_still_leaves_the_balanced_local_gap() -> None:
    assert pascadi_balanced_gap() == F(856, 191)


def test_mqw_initial_rectangle_has_exact_one_sixteenth_supremum() -> None:
    x, y = mqw_initial_rectangle_witness()
    assert (x, y) == (F(5, 8), F(5, 8))
    assert mqw_block_savings(x, y) == MQWBlockSavings(
        first=F(7, 48),
        second=F(1, 16),
        third=F(1, 16),
    )
    assert mqw_initial_rectangle_supremal_saving() == F(1, 16)


def test_mqw_witness_satisfies_every_size_condition_exactly() -> None:
    x, y = mqw_initial_rectangle_witness()
    assert x <= y + F(1, 4)
    assert F(7, 5) * x + y == F(3, 2)
    assert x + y <= F(5, 4)


def test_mqw_third_term_certifies_global_one_sixteenth_ceiling() -> None:
    # The theorem assumes x+y <= 5/4, so its third saving is always
    # at most 3(5/4)/16 - 11/64 = 1/16.  This is a certificate, not
    # a numerical grid search.
    ceiling = F(3, 16) * F(5, 4) - F(11, 64)
    assert ceiling == F(1, 16)


def test_elementary_large_sieve_loses_exactly_square_root_of_a() -> None:
    witnesses = boundary_witnesses()
    assert elementary_large_sieve_loss(witnesses["balanced_max_a"]) == F(5, 2)
    assert elementary_large_sieve_loss(witnesses["r_long"]) == F(2)
    assert elementary_large_sieve_loss(witnesses["s_long"]) == F(2)
    assert elementary_large_sieve_loss(witnesses["large_q_endpoint"]) == F(1, 2)


def test_two_sided_finite_mobius_decomposition_preserves_both_signs() -> None:
    limit = 80
    cutoff_r, cutoff_s = 3, 5
    depth_r = least_depth(cutoff_r, limit)
    depth_s = least_depth(cutoff_s, limit)
    for r in range(1, limit + 1):
        for s in range(1, limit + 1):
            assert two_sided_mobius_geometric_value(
                r,
                s,
                cutoff_r=cutoff_r,
                cutoff_s=cutoff_s,
                depth_r=depth_r,
                depth_s=depth_s,
            ) == naive_mobius(r) * naive_mobius(s)


def test_balanced_two_sided_dispersion_gaps_are_exact() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert dispersion_pointwise_mean_square_gap(box) == F(5)
    assert dispersion_random_benchmark_gap(box) == F(3, 2)


def test_full_fourfold_random_scale_has_half_power_margin() -> None:
    witnesses = boundary_witnesses()
    assert direct_fourfold_random_margin(witnesses["balanced_max_a"]) == F(1, 2)
    for box in witnesses.values():
        assert direct_fourfold_random_margin(box) >= F(1, 2)


def test_character_large_sieve_unit_stratum_keeps_balanced_half_a_loss() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert character_large_sieve_unit_gap(box) == F(5, 2)
    assert balanced_dual_low_mode_mobius_exponent(box) == F(2, 3)
    assert balanced_principal_character_mobius_exponent(box) == F(1, 3)


def test_induced_gauss_factor_cancels_the_cofactor_mobius_sign() -> None:
    for conductor in range(1, 31):
        for cofactor in range(1, 31):
            if gcd(conductor, cofactor) != 1:
                continue
            if naive_mobius(conductor * cofactor) == 0:
                continue
            assert induced_gauss_outer_mobius_sign(
                conductor, cofactor
            ) == naive_mobius(conductor)


def test_coprime_projection_and_global_principal_margin_are_exact() -> None:
    for modulus in range(1, 50):
        for value in range(-50, 51):
            assert coprime_indicator_via_mobius(value, modulus) == (
                1 if gcd(value, modulus) == 1 else 0
            )
    witnesses = boundary_witnesses()
    assert global_unit_principal_completion_margin(
        witnesses["balanced_max_a"]
    ) == F(0)
    for box in witnesses.values():
        assert global_unit_principal_completion_margin(box) >= 0


def test_squarefree_outer_mobius_ramanujan_divisor_identity() -> None:
    for modulus in range(1, 80):
        if naive_mobius(modulus) == 0:
            continue
        for frequency in range(-80, 81):
            expected = sum(
                d * naive_mobius(d)
                for d in range(1, gcd(modulus, abs(frequency)) + 1)
                if gcd(modulus, abs(frequency)) % d == 0
            )
            assert squarefree_outer_mobius_ramanujan(
                modulus, frequency
            ) == expected
            assert squarefree_outer_mobius_ramanujan(
                modulus, frequency
            ) == naive_mobius(modulus) * ramanujan_sum(
                modulus, frequency
            )
    assert nonunit_principal_long_factor_floor(
        boundary_witnesses()["balanced_max_a"]
    ) == F(5, 2)
    balanced = boundary_witnesses()["balanced_max_a"]
    assert nonunit_principal_h_boundary_slack(balanced) == 0
    assert nonunit_principal_trivial_loss(balanced) == F(2)
    assert nonunit_principal_equal_mobius_exponent(balanced) == F(7, 11)
    assert nonunit_principal_is_residual_face(balanced)
    assert not nonunit_principal_is_residual_face(
        boundary_witnesses()["large_q_endpoint"]
    )
    assert reverse_unit_solution_count_gap(balanced) == F(5, 2)
    assert reverse_unit_affine_progression_length(balanced) == F(5, 2)


def test_reverse_unit_top_divisor_has_exact_affine_solution_family() -> None:
    for n in range(1, 9):
        for k in range(1, 9):
            g = gcd(n, k)
            step = (k // g, n // g)
            for delta in range(-8, 9):
                solutions = [
                    (r, s)
                    for r in range(1, 33)
                    for s in range(1, 33)
                    if n * r + delta == k * s
                ]
                if delta % g:
                    assert solutions == []
                    continue
                for left, right in zip(solutions, solutions[1:]):
                    assert (right[0] - left[0], right[1] - left[1]) == step

            a0, b0 = step
            for residue in range(a0):
                r0 = next(r for r in range(1, a0 + 1) if b0 * r % a0 == residue)
                s0 = (b0 * r0 - residue) // a0
                for shift in range(-4, 5):
                    assert (
                        b0 * r0 - a0 * (s0 - shift)
                        == residue + a0 * shift
                    )


def test_centered_ramanujan_kernel_has_zero_unit_mean() -> None:
    for modulus in range(2, 48):
        mu_modulus = naive_mobius(modulus)
        if mu_modulus == 0:
            continue
        modulus_divisors = [
            d for d in range(1, modulus + 1) if modulus % d == 0
        ]
        assert sum(naive_mobius(d) for d in modulus_divisors) == 0
        assert sum(
            naive_mobius(modulus // d) for d in modulus_divisors
        ) == 0
        phi_modulus = sum(
            1 for r in range(1, modulus + 1) if gcd(r, modulus) == 1
        )
        for delta in range(1, 12):
            if gcd(delta, modulus) != 1:
                continue
            for n in range(-12, 13):
                centered_sum = sum(
                    F(
                        mu_modulus
                        * ramanujan_sum(
                            modulus,
                            n + delta * pow(r, -1, modulus),
                        )
                    )
                    - F(ramanujan_sum(modulus, n), phi_modulus)
                    for r in range(1, modulus + 1)
                    if gcd(r, modulus) == 1
                )
                assert centered_sum == 0


def test_nonunit_coprimality_dilation_is_exact_finite_mobius_inversion() -> None:
    for e in range(1, 20):
        if naive_mobius(e) == 0:
            continue
        e_divisors = [k for k in range(1, e + 1) if e % k == 0]
        for c in range(1, 20):
            if naive_mobius(c) == 0 or gcd(e, c) != 1:
                continue
            for h in range(-40, 41):
                expected = int(gcd(h, e * c) == 1)
                expanded = sum(
                    naive_mobius(k) * int(gcd(h // k, c) == 1)
                    for k in e_divisors
                    if h % k == 0
                )
                assert expanded == expected


def test_centered_and_principal_ramanujan_terms_recombine_exactly() -> None:
    for d in range(1, 12):
        if naive_mobius(d) == 0:
            continue
        for e in range(1, 12):
            if naive_mobius(e) == 0 or gcd(d, e) != 1:
                continue
            for c in range(1, 12):
                if (
                    naive_mobius(c) == 0
                    or gcd(d, c) != 1
                    or gcd(e, c) != 1
                ):
                    continue
                phi_c = sum(
                    1 for residue in range(1, c + 1) if gcd(residue, c) == 1
                )
                for n in range(-8, 9):
                    for shift in range(1, c + 1):
                        if gcd(shift, c) != 1:
                            continue
                        outer = F(naive_mobius(d) * naive_mobius(e))
                        shifted = ramanujan_sum(c, n + shift)
                        principal = outer * F(ramanujan_sum(c, n), phi_c)
                        centered = outer * (
                            naive_mobius(c) * shifted
                            - F(ramanujan_sum(c, n), phi_c)
                        )
                        assert centered + principal == (
                            outer * naive_mobius(c) * shifted
                        )


def test_delta_completed_congruence_has_self_dual_affine_family() -> None:
    for b in range(1, 9):
        for z in range(1, 9):
            g = gcd(b, z)
            step = (z // g, b // g)
            for v in range(-8, 9):
                solutions = [
                    (r, j)
                    for r in range(1, 33)
                    for j in range(1, 33)
                    if b * r - v == z * j
                ]
                if v % g:
                    assert solutions == []
                    continue
                for left, right in zip(solutions, solutions[1:]):
                    assert (right[0] - left[0], right[1] - left[1]) == step

    balanced = boundary_witnesses()["balanced_max_a"]
    lower = centered_dual_scales(balanced, F(5, 2))
    upper = centered_dual_scales(balanced, F(3))
    assert lower.cofactor == F(1, 2)
    assert lower.frequency == F(2)
    assert lower.residue == 0
    assert lower.quotient == F(1, 2)
    assert lower.progression == F(5, 2)
    assert lower.slope_penalty == F(1)
    assert upper.cofactor == 0
    assert upper.frequency == F(5, 2)
    assert upper.residue == F(1, 2)
    assert upper.quotient == F(1, 2)
    assert upper.progression == F(5, 2)
    assert upper.slope_penalty == F(1)
    assert wright_unbalanced_modulus_margin(
        balanced, F(5, 2), F(17, 33)
    ) == -F(21, 22)
    assert wright_unbalanced_modulus_margin(
        balanced, F(3), F(17, 33)
    ) == -F(79, 66)
    assert wright_unbalanced_modulus_margin(
        balanced, F(5, 2), F(45, 89)
    ) == -F(175, 178)
    assert wright_unbalanced_modulus_margin(
        balanced, F(3), F(45, 89)
    ) == -F(219, 178)
    assert centered_dual_common_mobius_exponent(
        balanced, F(5, 2)
    ) == F(7, 11)
    assert centered_dual_common_mobius_exponent(
        balanced, F(3)
    ) == F(7, 12)


def test_gcd_reduction_preserves_every_small_inverse_product_phase() -> None:
    for s in range(1, 41):
        if naive_mobius(s) == 0:
            continue
        for r in range(1, 2 * s + 1):
            if gcd(r, s) != 1:
                continue
            for h in range(1, 17):
                for delta in range(1, 17):
                    reduced = reduce_inverse_product_phase(r, s, h, delta)
                    assert reduced.d * reduced.e * reduced.modulus == s
                    assert gcd(reduced.d, reduced.e) == 1
                    assert gcd(reduced.d, reduced.modulus) == 1
                    assert gcd(reduced.e, reduced.modulus) == 1
                    assert gcd(reduced.h_reduced, reduced.modulus) == 1
                    assert gcd(reduced.delta_reduced, reduced.modulus) == 1
                    assert inverse_product_phase_mod_one(r, s, h, delta) == (
                        inverse_product_phase_mod_one(
                            r,
                            reduced.modulus,
                            reduced.h_reduced,
                            reduced.delta_reduced,
                        )
                    )


def test_pascadi_2024_direct_dispersion_bound_is_too_large() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert pascadi_2024_direct_dispersion_gap(box) == F(11, 2)


def test_research_note_contains_no_embedded_control_characters() -> None:
    note = (
        Path(__file__).parents[1]
        / "docs/research/2026-08-24-mobius-weighted-off-diagonal.md"
    ).read_text()
    forbidden = {
        character
        for character in note
        if ord(character) < 32 and character not in {"\n", "\t"}
    }
    assert forbidden == set()
