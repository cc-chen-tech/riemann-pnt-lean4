import sys
from fractions import Fraction as F
from math import gcd
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.audit_mobius_type_ii import (
    AdditiveDualBlockLedger,
    AdditiveShiftedChowlaLedger,
    BlomerPascadiMargins,
    BlomerPascadiUnbalancedLedger,
    CenteredCrtUnitMeanLedger,
    CenteredKloostermanCrtTerms,
    CenteredTransitionCompletionLedger,
    CentralCollisionLedger,
    CommonFactorMarginalLedger,
    CompletedProductPhaseReduction,
    CrossInverseFractionCollision,
    FareyCentralCollisionLedger,
    InverseFractionSeparation,
    KloostermanFractionTripleLedger,
    MobiusCharacterMeanSquareLedger,
    MQWBlockSavings,
    NearDeterminantBCLedger,
    NearDeterminantCoordinates,
    NearDeterminantDualCoordinates,
    PartiallyFixedModulusLedger,
    PascadiFullResidueSavings,
    PascadiModuliMargins,
    PrimeKloostermanLedger,
    PrimeSliceVarianceLedger,
    ScalarTypeIICutoffLedger,
    ShiftedPrimeMobiusCoordinates,
    ShiftedPrimeMobiusLedger,
    SquarefreeScalarGcdStratum,
    TransitionNumeratorCompletionLedger,
    TransitionNumeratorDualCoordinates,
    WrightFactorSavings,
    YoungCommonFactorLedger,
    YoungDualGcdLedger,
    YoungDualReciprocityLedger,
    YoungScalarTransitionLedger,
    additive_completion_axis_recombined,
    additive_completion_axis_row,
    additive_completion_axis_union,
    additive_completion_shifted,
    additive_completion_zero_mode,
    additive_completion_zero_mode_mobius_exponent,
    additive_dual_block_ledger,
    additive_dual_shift_phase,
    additive_product_completion,
    additive_shifted_chowla_ledger,
    ambient_centered_residue_collision_fourier,
    ambient_centered_residue_collision_fourier_formula,
    balanced_dual_low_mode_mobius_exponent,
    balanced_inverse_fraction_spacing_margin,
    balanced_principal_character_mobius_exponent,
    balanced_scalar_stratum_bettin_chandee_uniform_gap,
    blomer_pascadi_beats_best_trivial,
    blomer_pascadi_best_trivial_margins,
    blomer_pascadi_unbalanced_ledger,
    c_coefficient,
    centered_crt_unit_mean_ledger,
    centered_dual_common_mobius_exponent,
    centered_dual_parseval_covers,
    centered_dual_parseval_loss,
    centered_dual_scales,
    centered_inverse_cross_correlation,
    centered_inverse_cross_correlation_formula,
    centered_inverse_cross_correlation_gcd_formula,
    centered_inverse_cross_fourier,
    centered_inverse_cross_fourier_formula,
    centered_inverse_numerator_fourier,
    centered_inverse_numerator_fourier_formula,
    centered_kloosterman_crt_terms,
    centered_kloosterman_numerator_fourier,
    centered_kloosterman_numerator_fourier_formula,
    centered_kloosterman_transform,
    centered_residue_collision_fourier,
    centered_residue_collision_fourier_formula,
    centered_residue_collision_zero_formula,
    centered_transition_completion_ledger,
    centered_transition_diagonal_mass,
    centered_unit_congruence_boundary_majorant,
    centered_unit_congruence_sum,
    central_collision_ledger,
    central_cross_inverse_collision_margins,
    character_large_sieve_unit_gap,
    coherent_operator_large_sieve_exponent,
    coherent_operator_large_sieve_gap,
    coherent_operator_required_exponent,
    common_factor_marginal_ledger,
    completed_product_phase_reduction,
    coprimality_migrated_scalar_stratum_spectrum,
    coprime_centered_inverse_cross_fourier_factorization,
    coprime_indicator_via_mobius,
    cross_inverse_fraction_collision,
    direct_fourfold_random_margin,
    dispersion_pointwise_mean_square_gap,
    dispersion_random_benchmark_gap,
    double_unit_bilinear_sum,
    double_unit_divisor_spectrum,
    dual_unit_reciprocity_phase,
    dual_unit_reciprocity_phase_formula,
    elementary_large_sieve_loss,
    factorized_centered_kloosterman_numerator_fourier,
    factorized_centered_kloosterman_numerator_fourier_formula,
    farey_central_collision_ledger,
    farey_near_collision_count,
    farey_near_collision_divisor_bound,
    generalized_centered_dual_scales,
    global_unit_principal_completion_margin,
    induced_gauss_outer_mobius_sign,
    inverse_fraction_separation,
    inverse_lift_mobius_weight,
    inverse_product_phase_mod_one,
    large_common_divisor_pair_bound,
    linear_convolution_energy_on_multiples,
    linear_convolution_energy_on_multiples_majorant,
    migrate_nonprincipal_mobius_sign,
    mobius_character_mean_square_ledger,
    mobius_geometric_value,
    mobius_principal_density_value,
    mobius_two_cutoff_hyperbola_value,
    mobius_weighted_centered_double_unit_divisor_spectrum,
    mobius_weighted_double_unit_divisor_spectrum,
    mobius_weighted_double_unit_mean,
    mqw_block_savings,
    mqw_initial_rectangle_supremal_saving,
    mqw_initial_rectangle_witness,
    near_determinant_bettin_chandee_ledger,
    near_determinant_complete_delta_product_formula,
    near_determinant_complete_delta_product_sum,
    near_determinant_complete_reciprocal_sum,
    near_determinant_coordinates,
    near_determinant_dual_coordinates,
    near_determinant_reciprocal_parseval_sides,
    near_determinant_reciprocity_phase,
    near_determinant_reciprocity_phase_formula,
    nonunit_principal_equal_mobius_exponent,
    nonunit_principal_h_boundary_slack,
    nonunit_principal_is_residual_face,
    nonunit_principal_long_factor_floor,
    nonunit_principal_trivial_loss,
    partially_fixed_modulus_ledger,
    pascadi_2024_direct_dispersion_gap,
    pascadi_averaged_moduli_margins,
    pascadi_balanced_gap,
    pascadi_full_residue_savings,
    pascadi_optimal_delta,
    prime_kloosterman_average_ledger,
    prime_slice_variance_ledger,
    primitive_scalar_direct_value,
    primitive_scalar_recombined_value,
    ramanujan_mean_dyadic_divisor_majorant,
    ramanujan_mean_dyadic_sum,
    ramanujan_sum,
    rectangular_product_kernel,
    rectangular_product_multiplicities,
    rectangular_product_residue_energy,
    rectangular_product_residue_energy_majorant,
    reduce_inverse_product_phase,
    reduced_inverse_fraction_denominator,
    restricted_unit_fourier_lift,
    restricted_unit_fourier_lift_formula,
    reverse_unit_affine_progression_length,
    reverse_unit_solution_count_gap,
    scalar_incidence_energy,
    scalar_incidence_pair_energy_formula,
    scalar_stratum_bettin_chandee_ledger,
    scalar_type_i_absolute_exponent,
    scalar_type_ii_cutoff_ledger,
    shifted_prime_mobius_coordinates,
    shifted_prime_mobius_ledger,
    squarefree_normalized_ramanujan_mean_formula,
    squarefree_outer_mobius_ramanujan,
    squarefree_scalar_gcd_stratum,
    squarefree_scalar_stratum_completed_sum,
    squarefree_scalar_stratum_divisor_spectrum,
    transition_numerator_completion_ledger,
    transition_numerator_dual_coordinates,
    two_sided_centered_kloosterman_crt_terms,
    two_sided_mobius_geometric_value,
    unrestricted_fourier_lift,
    unrestricted_fourier_lift_formula,
    weighted_farey_collision_sum,
    weighted_inverse_collision_sum,
    weighted_inverse_product_box_sum,
    weighted_shifted_completion_box_sum,
    wright_factor_covers,
    wright_factor_savings,
    wright_unbalanced_modulus_margin,
    young_common_factor_ledger,
    young_dual_reciprocity_gcd_ledger,
    young_dual_reciprocity_ledger,
    young_scalar_transition_ledger,
)
from scripts.audit_mwkf_ranges import ExponentBox, boundary_witnesses


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


def test_blomer_pascadi_has_literal_critical_length_savings() -> None:
    assert blomer_pascadi_best_trivial_margins(F(1, 2)) == (
        BlomerPascadiMargins(
            first=F(1, 32),
            second=F(1, 32),
            third=F(1, 18),
        )
    )
    assert blomer_pascadi_beats_best_trivial(F(1, 2))


def test_blomer_pascadi_published_nontrivial_endpoints_are_exact() -> None:
    lower = blomer_pascadi_best_trivial_margins(F(13, 28))
    upper = blomer_pascadi_best_trivial_margins(F(7, 12))
    assert lower.first == 0
    assert upper.third == 0
    assert not blomer_pascadi_beats_best_trivial(F(13, 28))
    assert not blomer_pascadi_beats_best_trivial(F(7, 12))
    assert blomer_pascadi_beats_best_trivial(F(13, 28) + F(1, 10_000))
    assert blomer_pascadi_beats_best_trivial(F(7, 12) - F(1, 10_000))


def test_blomer_pascadi_does_not_cover_the_full_residue_scale() -> None:
    margins = blomer_pascadi_best_trivial_margins(F(1))
    assert margins == BlomerPascadiMargins(
        first=-F(1, 32),
        second=-F(1, 8),
        third=-F(5, 18),
    )
    assert not blomer_pascadi_beats_best_trivial(F(1))


def test_pascadi_averaged_moduli_corollary_covers_only_short_fourier_boxes() -> None:
    critical = pascadi_averaged_moduli_margins(
        length=F(1, 2), fixed_modulus=F(1), amplifier=F(1, 2)
    )
    assert critical == PascadiModuliMargins(first=F(1, 12), second=F(1, 12))
    assert critical.best == F(1, 12)

    no_fixed_modulus = pascadi_averaged_moduli_margins(
        length=F(1, 2), fixed_modulus=F(0), amplifier=F(0)
    )
    assert no_fixed_modulus.best == 0


def test_pascadi_averaged_moduli_corollary_worsens_full_residue_boxes() -> None:
    for fixed_modulus in (F(0), F(1, 4), F(1, 2), F(1)):
        for amplifier in (F(0), fixed_modulus / 2, fixed_modulus):
            margins = pascadi_averaged_moduli_margins(
                length=F(1),
                fixed_modulus=fixed_modulus,
                amplifier=amplifier,
            )
            assert margins.best == -(1 + amplifier) / 6
            assert margins.best < 0


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


def test_coherent_modulus_operator_ledger_recovers_the_same_exact_loss() -> None:
    witnesses = boundary_witnesses()
    balanced = witnesses["balanced_max_a"]
    assert coherent_operator_required_exponent(balanced) == F(2)
    assert coherent_operator_large_sieve_exponent(balanced) == F(9, 2)
    assert coherent_operator_large_sieve_gap(balanced) == F(5, 2)
    for box in witnesses.values():
        assert coherent_operator_large_sieve_gap(box) == (
            elementary_large_sieve_loss(box)
        )


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


def test_two_cutoff_hyperbola_identity_has_no_cross_term_or_remainder() -> None:
    for cutoff_left in range(1, 8):
        for cutoff_right in range(1, 8):
            for n in range(max(cutoff_left, cutoff_right) + 1, 121):
                assert mobius_two_cutoff_hyperbola_value(
                    n,
                    cutoff_left=cutoff_left,
                    cutoff_right=cutoff_right,
                ) == naive_mobius(n)


def test_primitive_scalar_layers_recombine_into_sparse_full_modulus() -> None:
    for modulus in range(2, 61):
        if naive_mobius(modulus) == 0:
            continue
        all_factors = tuple(
            divisor
            for divisor in range(1, modulus + 1)
            if modulus % divisor == 0
        )
        factor_families = (all_factors, all_factors[::2], all_factors[1::2])
        for scalar_factors in factor_families:
            for shift in range(1, min(modulus, 5)):
                if gcd(shift, modulus) != 1:
                    continue
                for frequency in range(1, 4):
                    for interval_length in range(1, 9):
                        direct = primitive_scalar_direct_value(
                            modulus,
                            shift,
                            frequency,
                            interval_length,
                            scalar_factors,
                        )
                        recombined = primitive_scalar_recombined_value(
                            modulus,
                            shift,
                            frequency,
                            interval_length,
                            scalar_factors,
                        )
                        assert abs(direct - recombined) < 1e-8


def test_scalar_incidence_energy_has_exact_lcm_pair_formula() -> None:
    for modulus in range(2, 61):
        if naive_mobius(modulus) == 0:
            continue
        all_factors = tuple(
            divisor
            for divisor in range(1, modulus + 1)
            if modulus % divisor == 0
        )
        for scalar_factors in (all_factors, all_factors[::2], all_factors[1::2]):
            for interval_length in range(1, 21):
                assert scalar_incidence_energy(
                    modulus,
                    interval_length,
                    scalar_factors,
                ) == scalar_incidence_pair_energy_formula(
                    modulus,
                    interval_length,
                    scalar_factors,
                )


def test_scalar_type_i_absolute_value_never_saves_the_half_power() -> None:
    scalar_length = F(1, 2)
    for left_quarters in range(3):
        for right_quarters in range(3):
            left_cutoff = F(left_quarters, 4)
            right_cutoff = F(right_quarters, 4)
            exponent = scalar_type_i_absolute_exponent(
                scalar_length,
                left_cutoff,
                right_cutoff,
            )
            assert exponent == max(
                scalar_length,
                left_cutoff + right_cutoff,
            )
            assert exponent >= scalar_length


def test_symmetric_type_ii_cutoff_creates_long_long_near_determinant() -> None:
    assert scalar_type_ii_cutoff_ledger(
        r_length=F(3),
        reduced_modulus=F(5, 2),
        scalar_length=F(1, 2),
        shift_length=F(2),
        left_cutoff=F(1, 4),
        right_cutoff=F(1, 4),
    ) == ScalarTypeIICutoffLedger(
        divisor_product_floor=F(1, 2),
        divisor_product_vs_scalar=F(0),
        quotient_ceiling=F(5, 2),
        fixed_divisor_quotient_window=F(3, 2),
        rational_distance=F(-1),
    )


def test_bettin_chandee_misses_near_determinant_even_with_free_scalar_sum() -> None:
    perfect_scalar = near_determinant_bettin_chandee_ledger(
        long_numerator=F(3),
        long_modulus=F(5, 2),
        product_length=F(9, 2),
        scalar_coefficient_cost=F(0),
        target=F(9),
    )
    assert perfect_scalar == NearDeterminantBCLedger(
        coefficient_norm=F(5),
        first_parenthetical=F(17, 4),
        second_parenthetical=F(75, 16),
        large_phase_penalty=F(0),
        theorem_bound=F(37, 4),
        target=F(9),
        gap=F(1, 4),
    )
    trivial_scalar = near_determinant_bettin_chandee_ledger(
        long_numerator=F(3),
        long_modulus=F(5, 2),
        product_length=F(9, 2),
        scalar_coefficient_cost=F(1, 2),
        target=F(9),
    )
    assert trivial_scalar.theorem_bound == F(39, 4)
    assert trivial_scalar.gap == F(3, 4)


def test_near_determinant_has_one_affine_solution_line() -> None:
    for divisor_product in range(2, 13):
        for scalar_factor in range(1, 10):
            if gcd(divisor_product, scalar_factor) != 1:
                continue
            for determinant in range(1, 10):
                if gcd(determinant, divisor_product * scalar_factor) != 1:
                    continue
                base = near_determinant_coordinates(
                    divisor_product,
                    scalar_factor,
                    determinant,
                    0,
                )
                assert base == NearDeterminantCoordinates(
                    base_modulus=base.base_modulus,
                    base_quotient=base.base_quotient,
                    modulus=base.base_modulus,
                    quotient=base.base_quotient,
                )
                for parameter in range(7):
                    coordinates = near_determinant_coordinates(
                        divisor_product,
                        scalar_factor,
                        determinant,
                        parameter,
                    )
                    assert (
                        divisor_product * coordinates.quotient
                        - scalar_factor * coordinates.modulus
                        == determinant
                    )
                    assert coordinates.modulus == (
                        base.base_modulus + divisor_product * parameter
                    )
                    assert coordinates.quotient == (
                        base.base_quotient + scalar_factor * parameter
                    )


def test_near_determinant_parameter_is_complete_mod_d_and_reciprocal() -> None:
    for divisor_product in range(2, 11):
        for scalar_factor in range(1, 8):
            if gcd(divisor_product, scalar_factor) != 1:
                continue
            for determinant in range(2, 12):
                if gcd(determinant, divisor_product * scalar_factor) != 1:
                    continue
                residues = {
                    near_determinant_coordinates(
                        divisor_product,
                        scalar_factor,
                        determinant,
                        parameter,
                    ).modulus
                    % determinant
                    for parameter in range(determinant)
                }
                assert residues == set(range(determinant))
                for parameter in range(determinant):
                    modulus = near_determinant_coordinates(
                        divisor_product,
                        scalar_factor,
                        determinant,
                        parameter,
                    ).modulus
                    if modulus < 2 or gcd(modulus, determinant) != 1:
                        continue
                    for numerator in range(-3, 4):
                        direct = near_determinant_reciprocity_phase(
                            modulus,
                            determinant,
                            numerator,
                        )
                        formula = near_determinant_reciprocity_phase_formula(
                            modulus,
                            determinant,
                            numerator,
                        )
                        assert abs(direct - formula) < 1e-8


def test_complete_near_determinant_reciprocal_core_is_ramanujan() -> None:
    for divisor_product in range(2, 11):
        for scalar_factor in range(1, 8):
            if gcd(divisor_product, scalar_factor) != 1:
                continue
            for determinant in range(2, 12):
                if gcd(determinant, divisor_product * scalar_factor) != 1:
                    continue
                for numerator in range(-4, 5):
                    complete = near_determinant_complete_reciprocal_sum(
                        divisor_product,
                        scalar_factor,
                        determinant,
                        numerator,
                    )
                    assert abs(complete - ramanujan_sum(determinant, numerator)) < 1e-8


def test_near_determinant_reciprocal_transform_has_exact_parseval_energy() -> None:
    for divisor_product in range(2, 9):
        for scalar_factor in range(1, 7):
            if gcd(divisor_product, scalar_factor) != 1:
                continue
            for determinant in range(2, 11):
                if gcd(determinant, divisor_product * scalar_factor) != 1:
                    continue
                weights = tuple(
                    complex(parameter - 2, (parameter * parameter + 1) % 5 - 2)
                    for parameter in range(determinant)
                )
                transform_energy, coefficient_energy = (
                    near_determinant_reciprocal_parseval_sides(
                        divisor_product,
                        scalar_factor,
                        determinant,
                        weights,
                    )
                )
                assert abs(transform_energy - coefficient_energy) < 1e-7


def test_product_residue_energy_keeps_exact_boundaries() -> None:
    for h_length in range(1, 10):
        for delta_length in range(1, 9):
            multiplicities = rectangular_product_multiplicities(
                h_length, delta_length
            )
            product_energy = sum(value * value for value in multiplicities.values())
            for modulus in range(2, 10):
                residue_energy = rectangular_product_residue_energy(
                    h_length, delta_length, modulus
                )
                majorant = rectangular_product_residue_energy_majorant(
                    h_length, delta_length, modulus
                )
                assert residue_energy <= majorant
                assert majorant == (
                    (h_length * delta_length + modulus - 1) // modulus
                ) * product_energy


def test_complete_delta_box_uses_only_unit_frequency_and_collapses() -> None:
    for divisor_product in range(2, 9):
        for scalar_factor in range(1, 7):
            if gcd(divisor_product, scalar_factor) != 1:
                continue
            for determinant in range(2, 11):
                if gcd(determinant, divisor_product * scalar_factor) != 1:
                    continue
                weights = tuple(
                    complex((3 * parameter + 1) % 7 - 3, parameter % 3 - 1)
                    for parameter in range(determinant)
                )
                for h_length in range(1, 2 * determinant + 3):
                    for periods in (1, 2):
                        delta_length = periods * determinant
                        direct = near_determinant_complete_delta_product_sum(
                            divisor_product,
                            scalar_factor,
                            determinant,
                            h_length,
                            delta_length,
                            weights,
                        )
                        formula = near_determinant_complete_delta_product_formula(
                            divisor_product,
                            scalar_factor,
                            determinant,
                            h_length,
                            delta_length,
                            weights,
                        )
                        assert abs(direct - formula) < 1e-7


def test_partially_fixed_modulus_theorem_still_loses_near_window_density() -> None:
    assert partially_fixed_modulus_ledger(
        long_modulus=F(5, 2),
        quotient=F(5, 2),
        fixed_divisor=F(1, 2),
        product_numerator=F(9, 2),
        short_factor_triangle=F(1),
        target=F(9),
    ) == PartiallyFixedModulusLedger(
        coefficient_norm=F(19, 4),
        geometric_factor=F(19, 4),
        fixed_factor=F(1, 8),
        first_term=F(-5, 16),
        second_term=F(-1, 4),
        third_term=F(-17, 40),
        fourth_term=F(-4, 5),
        fifth_term=F(-5, 16),
        fixed_block_bound=F(75, 8),
        global_bound=F(83, 8),
        target=F(9),
        gap=F(11, 8),
    )


def test_delta_poisson_dual_modes_share_one_affine_lattice() -> None:
    for divisor_product in range(2, 11):
        for scalar_factor in range(1, 8):
            if gcd(divisor_product, scalar_factor) != 1:
                continue
            for determinant in range(2, 12):
                if gcd(determinant, divisor_product * scalar_factor) != 1:
                    continue
                for parameter in range(6):
                    for dual_frequency in range(-3, 4):
                        for dual_quotient in range(-2, 4):
                            determinant_coordinates = near_determinant_coordinates(
                                divisor_product,
                                scalar_factor,
                                determinant,
                                parameter,
                            )
                            dual = near_determinant_dual_coordinates(
                                divisor_product,
                                scalar_factor,
                                determinant,
                                parameter,
                                dual_frequency,
                                dual_quotient,
                            )
                            assert dual == NearDeterminantDualCoordinates(
                                modulus=determinant_coordinates.modulus,
                                determinant_quotient=(
                                    determinant_coordinates.quotient
                                ),
                                numerator=(
                                    dual_quotient * determinant
                                    - dual_frequency
                                    * determinant_coordinates.modulus
                                ),
                                dual_quotient=dual_quotient,
                            )
                            assert (
                                divisor_product * dual.determinant_quotient
                                - scalar_factor * dual.modulus
                                == determinant
                            )
                            assert (
                                dual.numerator
                                + dual_frequency * dual.modulus
                                == dual.dual_quotient * determinant
                            )


def test_ordinary_character_large_sieve_leaves_quarter_power_gap() -> None:
    assert mobius_character_mean_square_ledger(
        progression_modulus=F(1, 2),
        scalar_length=F(1, 2),
        long_length=F(5, 2),
        required_saving=F(1, 2),
    ) == MobiusCharacterMeanSquareLedger(
        raw_progression_bound=F(3),
        bombieri_vinogradov_bound=F(3),
        short_character_energy=F(1),
        long_character_energy=F(9, 2),
        ordinary_large_sieve_bound=F(11, 4),
        required_bound=F(5, 2),
        ordinary_saving=F(1, 4),
        required_saving=F(1, 2),
        gap=F(1, 4),
        required_long_character_energy=F(4),
    )


def test_principal_density_has_an_unavoidable_prime_slice() -> None:
    for cutoff_left, cutoff_right in ((1, 1), (2, 5), (7, 3), (11, 13)):
        for prime in (17, 19, 23, 29, 31, 37, 41, 43):
            if prime <= max(cutoff_left, cutoff_right):
                continue
            assert mobius_principal_density_value(
                prime,
                cutoff_left=cutoff_left,
                cutoff_right=cutoff_right,
            ) == F(-1)


def test_kloosterman_over_primes_does_not_fill_scalar_half_power() -> None:
    assert prime_kloosterman_average_ledger(
        modulus=F(5, 2),
        prime_length=F(3),
        required_saving=F(1, 2),
    ) == PrimeKloostermanLedger(
        first_term=F(5),
        second_term=F(26, 5),
        third_term=F(61, 12),
        theorem_bound=F(26, 5),
        trivial_bound=F(11, 2),
        theorem_saving=F(3, 10),
        required_saving=F(1, 2),
        gap=F(1, 5),
    )
    assert prime_kloosterman_average_ledger(
        modulus=F(5, 2),
        prime_length=F(2),
        required_saving=F(1, 2),
    ) == PrimeKloostermanLedger(
        first_term=F(35, 8),
        second_term=F(43, 10),
        third_term=F(157, 36),
        theorem_bound=F(35, 8),
        trivial_bound=F(9, 2),
        theorem_saving=F(1, 8),
        required_saving=F(1, 2),
        gap=F(3, 8),
    )


def test_prime_slice_selberg_variance_and_density_barriers_are_exact() -> None:
    assert prime_slice_variance_ledger(
        ambient_length=F(3),
        shift_length=F(2),
        scalar_length=F(1, 2),
    ) == PrimeSliceVarianceLedger(
        relative_interval=F(-1),
        trivial_bound=F(5),
        target_bound=F(9, 2),
        unconditional_variance=F(7),
        unconditional_cauchy_bound=F(5),
        unconditional_gap=F(1, 2),
        rh_variance=F(5),
        rh_cauchy_bound=F(4),
        rh_margin=F(1, 2),
        density_required_mertens=F(5, 2),
        density_required_ratio=F(5, 6),
        density_required_saving=F(1, 2),
    )


def test_published_shifted_prime_mobius_average_has_no_power_saving() -> None:
    assert shifted_prime_mobius_ledger(
        ambient_length=F(3),
        shift_length=F(2),
        scalar_length=F(1, 2),
    ) == ShiftedPrimeMobiusLedger(
        raw_bound=F(5),
        published_power_bound=F(5),
        target_bound=F(9, 2),
        published_power_saving=F(0),
        required_power_saving=F(1, 2),
        gap=F(1, 2),
    )


def test_shifted_prime_mobius_change_of_variables_is_exact() -> None:
    for shift_range in range(1, 9):
        for shift in range(1, shift_range + 1):
            for base in range(shift_range + 1, 2 * shift_range + 8):
                coordinates = shifted_prime_mobius_coordinates(
                    base=base,
                    shift=shift,
                    shift_range=shift_range,
                )
                assert coordinates == ShiftedPrimeMobiusCoordinates(
                    mobius_shift=shift_range - shift,
                    translated_base=base + shift - shift_range,
                )
                assert coordinates.translated_base + coordinates.mobius_shift == base
                assert coordinates.translated_base + shift_range == base + shift


def test_transition_numerator_completion_keeps_exact_scalar_half_gap() -> None:
    assert transition_numerator_completion_ledger(
        raw_bound=F(23, 2),
        numerator_length=F(2),
        modulus=F(5, 2),
        numerator_sum_length=F(5, 2),
        target=F(9),
    ) == TransitionNumeratorCompletionLedger(
        dual_length=F(0),
        numerator_saving=F(2),
        completed_bound=F(19, 2),
        target=F(9),
        gap=F(1, 2),
    )


def test_transition_numerator_dual_congruence_forces_exact_dilation() -> None:
    for determinant in tuple(range(-8, 0)) + tuple(range(1, 9)):
        for dual_frequency in tuple(range(-5, 0)) + tuple(range(1, 6)):
            numerator = dual_frequency * determinant
            if numerator <= 0:
                continue
            modulus = 2 * numerator + 1
            if gcd(determinant, modulus) != 1:
                continue
            assert transition_numerator_dual_coordinates(
                modulus=modulus,
                determinant=determinant,
                numerator=numerator,
                dual_frequency=dual_frequency,
            ) == TransitionNumeratorDualCoordinates(
                dual_frequency=dual_frequency,
                determinant=determinant,
                numerator=numerator,
            )


def test_centered_transition_completion_keeps_the_short_interval_point_mass() -> None:
    assert centered_transition_completion_ledger(
        modulus=F(5, 2),
        determinant_length=F(2),
    ) == CenteredTransitionCompletionLedger(
        point_mass=F(2),
        uniform_background=F(3, 2),
        point_over_background=F(1, 2),
    )


def test_centered_transition_diagonal_is_not_a_vanishing_d_major_arc() -> None:
    # For a prime q>D and ell=1, the completed centered kernel on the
    # aligned initial boxes is D-D^2/phi(q), not zero.  At q/D=T^(1/2)
    # its uniform background is exactly a half-power smaller.
    for modulus in (5, 7, 11, 13, 17):
        for length in range(1, modulus):
            assert centered_transition_diagonal_mass(
                modulus,
                length,
            ) == F(length) - F(length * length, modulus - 1)
    assert centered_transition_diagonal_mass(11, 3) == F(21, 10)


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


def test_generalized_centered_ramanujan_divisor_expansion_is_exact() -> None:
    for c in range(1, 24):
        if naive_mobius(c) == 0:
            continue
        phi_c = sum(1 for residue in range(1, c + 1) if gcd(residue, c) == 1)
        divisors_c = [j for j in range(1, c + 1) if c % j == 0]
        for n in range(-20, 21):
            for shift in range(1, c + 1):
                if gcd(shift, c) != 1:
                    continue
                centered = (
                    naive_mobius(c) * ramanujan_sum(c, n + shift)
                    - F(ramanujan_sum(c, n), phi_c)
                )
                divisor_expansion = sum(
                    j
                    * (
                        naive_mobius(j) * int((n + shift) % j == 0)
                        - F(naive_mobius(c // j), phi_c)
                        * int(n % j == 0)
                    )
                    for j in divisors_c
                )
                assert centered == divisor_expansion


def test_nonprincipal_mobius_sign_migration_is_a_finite_bijection() -> None:
    for d in range(1, 14):
        for e in range(1, 18):
            for c in range(1, 14):
                if (
                    naive_mobius(d * e * c) == 0
                    or gcd(d, e) != 1
                    or gcd(d, c) != 1
                    or gcd(e, c) != 1
                ):
                    continue
                for k in range(1, e + 1):
                    if e % k != 0:
                        continue
                    for delta_reduced in range(1, 16):
                        if gcd(delta_reduced, c) != 1:
                            continue
                        migrated = migrate_nonprincipal_mobius_sign(
                            d, e, c, delta_reduced, k
                        )
                        assert migrated.s == d * e * c
                        assert migrated.delta == e * delta_reduced
                        assert migrated.gcd_part == gcd(
                            migrated.shifted_delta,
                            migrated.residual_modulus,
                        )
                        assert migrated.centered_modulus == (
                            migrated.residual_modulus // migrated.gcd_part
                        )
                        assert migrated.mobius_sign == naive_mobius(
                            migrated.dilation
                        )
                        assert e == migrated.gcd_part * migrated.dilation
                        assert delta_reduced == (
                            migrated.shifted_delta // migrated.gcd_part
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

    low_divisor_face = ExponentBox(
        rho=F(2),
        sigma=F(2),
        m=F(1, 2),
        k=F(1, 2),
        ell=F(1, 2),
        h=F(3, 2),
        kappa=F(0),
    )
    assert centered_dual_parseval_loss(low_divisor_face, F(1, 2)) == 0
    assert centered_dual_parseval_covers(low_divisor_face, F(1, 2))
    assert centered_dual_parseval_loss(low_divisor_face, F(1)) == F(1, 2)
    assert not centered_dual_parseval_covers(low_divisor_face, F(1))

    generalized = generalized_centered_dual_scales(
        balanced,
        modulus=F(5, 2),
        delta_gcd=F(1, 2),
        mobius_divisor=F(1, 4),
    )
    assert generalized.raw_frequency == F(9, 4)
    assert generalized.product_frequency == F(5, 2)
    assert generalized.residue == F(1, 2)
    assert generalized.quotient == F(1)
    assert generalized.progression == F(2)
    assert generalized.residue + balanced.rho == (
        generalized.quotient + F(5, 2)
    )


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


def test_fixed_numerator_inverse_fraction_congruence_is_exact() -> None:
    certificate = inverse_fraction_separation(r=19, s=11, t=16)
    assert certificate == InverseFractionSeparation(
        numerator=-9,
        denominator=176,
        distance=F(9, 176),
        congruence_quotient=-1,
    )
    assert (
        19 * certificate.numerator - (16 - 11)
        == certificate.congruence_quotient * certificate.denominator
    )


def test_balanced_fixed_numerator_fractions_have_inverse_linear_spacing() -> None:
    for lower in range(2, 21):
        for r in range(lower + 1, 2 * lower + 1):
            for s in range(lower + 1, 2 * lower + 1):
                for t in range(lower + 1, 2 * lower + 1):
                    if s == t or gcd(r, s * t) != 1:
                        continue
                    certificate = inverse_fraction_separation(r, s, t)
                    assert certificate.congruence_quotient != 0
                    assert balanced_inverse_fraction_spacing_margin(
                        r, s, t, lower=lower
                    ) >= 0


def test_equal_moduli_are_the_only_zero_fixed_numerator_separation() -> None:
    for modulus in range(2, 30):
        for r in range(1, 2 * modulus):
            if gcd(r, modulus) != 1:
                continue
            certificate = inverse_fraction_separation(r, modulus, modulus)
            assert certificate.numerator == 0
            assert certificate.distance == 0


def test_cross_numerator_inverse_fraction_congruence_is_exact() -> None:
    certificate = cross_inverse_fraction_collision(r=5, s=7, r_prime=11, t=8)
    assert certificate == CrossInverseFractionCollision(
        numerator=3,
        denominator=56,
        distance=F(3, 56),
        congruence_quotient=2,
    )
    assert (
        5 * 11 * certificate.numerator - (11 * 8 - 5 * 7)
        == certificate.congruence_quotient * certificate.denominator
    )
    assert (5 * certificate.numerator - 8) * (
        11 + certificate.congruence_quotient * 7
    ) == 5 * 7 * (
        certificate.numerator * certificate.congruence_quotient - 1
    )


def test_cross_numerator_factorization_holds_exhaustively() -> None:
    for r in range(1, 15):
        for s in range(2, 15):
            if gcd(r, s) != 1:
                continue
            for r_prime in range(1, 15):
                for t in range(2, 15):
                    if gcd(r_prime, t) != 1:
                        continue
                    certificate = cross_inverse_fraction_collision(
                        r, s, r_prime, t
                    )
                    k = certificate.numerator
                    ell = certificate.congruence_quotient
                    assert r * r_prime * k - (r_prime * t - r * s) == (
                        ell * s * t
                    )
                    assert (r * k - t) * (r_prime + ell * s) == (
                        r * s * (k * ell - 1)
                    )


def test_cross_numerator_degenerate_factorizations_are_real_diagonals() -> None:
    positive = cross_inverse_fraction_collision(5, 7, 3, 5)
    assert (positive.numerator, positive.congruence_quotient) == (1, 1)
    assert 5 * positive.numerator - 5 == 0

    negative = cross_inverse_fraction_collision(5, 7, 7, 2)
    assert (negative.numerator, negative.congruence_quotient) == (-1, -1)
    assert 7 + negative.congruence_quotient * 7 == 0


def test_balanced_central_collision_bounds_are_exact_rational_margins() -> None:
    # This literal collision has distance 1/42 <= 1/16 and lies in
    # 4 < r,r' <= 8 and 4 < s,t <= 8.
    margins = central_cross_inverse_collision_margins(
        r=5,
        s=6,
        r_prime=6,
        t=7,
        lower_r=4,
        lower_s=4,
        product_length=16,
    )
    assert margins.numerator_margin == F(3)
    assert margins.quotient_margin == F(7)


def test_balanced_central_collision_bounds_hold_on_small_boxes() -> None:
    for lower in range(2, 13):
        for r in range(lower + 1, 2 * lower + 1):
            for s in range(lower + 1, 2 * lower + 1):
                if gcd(r, s) != 1:
                    continue
                for r_prime in range(lower + 1, 2 * lower + 1):
                    for t in range(lower + 1, 2 * lower + 1):
                        if gcd(r_prime, t) != 1:
                            continue
                        certificate = cross_inverse_fraction_collision(
                            r, s, r_prime, t
                        )
                        for product_length in (1, lower, lower * lower):
                            if certificate.distance > F(1, product_length):
                                continue
                            margins = central_cross_inverse_collision_margins(
                                r,
                                s,
                                r_prime,
                                t,
                                lower_r=lower,
                                lower_s=lower,
                                product_length=product_length,
                            )
                            assert margins.numerator_margin >= 0
                            assert margins.quotient_margin >= 0


def test_factor_degenerate_cross_collisions_are_two_small_diagonals() -> None:
    for lower in range(2, 21):
        points = [
            (r, s)
            for r in range(lower + 1, 2 * lower + 1)
            for s in range(lower + 1, 2 * lower + 1)
            if gcd(r, s) == 1
        ]
        degenerate_count = 0
        for r, s in points:
            for r_prime, t in points:
                certificate = cross_inverse_fraction_collision(
                    r, s, r_prime, t
                )
                k = certificate.numerator
                ell = certificate.congruence_quotient
                if k * ell != 1:
                    continue
                degenerate_count += 1
                assert (k, ell) in {(1, 1), (-1, -1)}
                assert (k == 1 and t == r) or (k == -1 and r_prime == s)
        assert degenerate_count <= 2 * lower * lower


def test_balanced_central_collision_ledger_exposes_one_power_counting_gap() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert central_collision_ledger(box) == CentralCollisionLedger(
        numerator=F(1),
        quotient=F(1),
        degenerate_count=F(6),
        divisor_parameter_count=F(8),
        random_collision_count=F(7),
        counting_gap=F(1),
    )


def test_product_kernel_matches_divisor_multiplicity_form_numerically() -> None:
    for h_length in range(1, 8):
        for delta_length in range(1, 8):
            multiplicities = rectangular_product_multiplicities(
                h_length, delta_length
            )
            assert sum(multiplicities.values()) == h_length * delta_length
            for denominator in range(2, 10):
                phase = F(1, denominator)
                direct = rectangular_product_kernel(
                    h_length, delta_length, phase
                )
                collapsed = sum(
                    multiplicity
                    * rectangular_product_kernel(1, 1, phase * product)
                    for product, multiplicity in multiplicities.items()
                )
                assert abs(direct - collapsed) < 1e-10


def test_product_kernel_numerically_realizes_noncentral_rational_resonance() -> None:
    for denominator in (5, 7, 11):
        phase = F(1, denominator)
        kernel = rectangular_product_kernel(denominator, denominator, phase)
        assert abs(kernel - denominator) < 1e-9
        assert phase > F(1, denominator * denominator)


def test_inverse_fraction_determinant_has_exact_gcd_structure() -> None:
    for s in range(2, 30):
        if naive_mobius(s) == 0:
            continue
        for t in range(2, 30):
            if naive_mobius(t) == 0:
                continue
            common = gcd(s, t)
            for u in range(1, s):
                if gcd(u, s) != 1:
                    continue
                for v in range(1, t):
                    if gcd(v, t) != 1:
                        continue
                    determinant = u * t - v * s
                    assert gcd(determinant, s) == common
                    assert gcd(determinant, t) == common
                    assert reduced_inverse_fraction_denominator(
                        u, s, v, t
                    ) == (s * t) // gcd(determinant, s * t)
                    assert reduced_inverse_fraction_denominator(
                        u, s, v, t
                    ) == (s * t // common) // gcd(
                        determinant // common, common
                    )


def test_farey_central_collision_divisor_bound_is_a_finite_majorant() -> None:
    for lower in range(2, 13):
        for numerator_bound in range(lower + 1):
            assert farey_near_collision_count(lower, numerator_bound) <= (
                farey_near_collision_divisor_bound(lower, numerator_bound)
            )


def test_farey_parameterization_removes_the_balanced_one_power_gap() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert farey_central_collision_ledger(box) == FareyCentralCollisionLedger(
        numerator=F(1),
        lift_multiplicity=F(0),
        elementary_count=F(7),
        random_collision_count=F(7),
        counting_gap=F(0),
    )


def test_balanced_inverse_lift_weights_are_zero_or_one_mobius_sign() -> None:
    for lower in range(2, 20):
        for modulus in range(lower + 1, 2 * lower + 1):
            for numerator in range(1, modulus):
                if gcd(numerator, modulus) != 1:
                    continue
                assert abs(
                    inverse_lift_mobius_weight(
                        numerator, modulus, lower_r=lower
                    )
                ) <= 1


def test_four_mobius_collision_sum_has_exact_signed_farey_coordinates() -> None:
    for lower_r in range(2, 7):
        for lower_s in range(2, 7):
            for numerator_bound in range(4):
                assert weighted_inverse_collision_sum(
                    lower_r, lower_s, numerator_bound
                ) == weighted_farey_collision_sum(
                    lower_r, lower_s, numerator_bound
                )


def test_additive_completion_matches_direct_evaluation_numerically() -> None:
    for modulus in range(2, 13):
        for r in range(1, 2 * modulus):
            if gcd(r, modulus) != 1:
                continue
            for h_length in range(1, 6):
                for delta_length in range(1, 6):
                    direct = rectangular_product_kernel(
                        h_length,
                        delta_length,
                        -F(pow(r, -1, modulus), modulus),
                    )
                    completed = additive_product_completion(
                        r, modulus, h_length, delta_length
                    )
                    assert abs(direct - completed) < 1e-9


def test_additive_completion_zero_mode_hits_the_two_thirds_barrier() -> None:
    assert additive_completion_zero_mode(11, 7, 5) == F(35, 11)
    balanced = boundary_witnesses()["balanced_max_a"]
    assert additive_completion_zero_mode_mobius_exponent(balanced) == F(2, 3)


def test_additive_completion_is_exactly_a_shifted_chowla_phase() -> None:
    for modulus in range(2, 13):
        for r in range(1, 2 * modulus):
            if gcd(r, modulus) != 1:
                continue
            for a in range(modulus):
                for b in range(modulus):
                    phase = additive_dual_shift_phase(r, modulus, a, b)
                    assert phase.original == phase.shifted
                    assert phase.shift == r - modulus
            for h_length in range(1, 5):
                for delta_length in range(1, 5):
                    assert abs(
                        additive_product_completion(
                            r, modulus, h_length, delta_length
                        )
                        - additive_completion_shifted(
                            r, modulus, h_length, delta_length
                        )
                    ) < 1e-9


def test_weighted_box_has_exact_moving_shift_endpoints() -> None:
    for lower_r in range(2, 6):
        for lower_s in range(2, 6):
            for h_length in range(1, 4):
                for delta_length in range(1, 4):
                    assert abs(
                        weighted_inverse_product_box_sum(
                            lower_r, lower_s, h_length, delta_length
                        )
                        - weighted_shifted_completion_box_sum(
                            lower_r, lower_s, h_length, delta_length
                        )
                    ) < 1e-8


def test_additive_completion_axes_recombine_zero_mode_exactly() -> None:
    for modulus in range(2, 17):
        for h_length in range(1, 2 * modulus + 1):
            for delta_length in range(1, 2 * modulus + 1):
                assert additive_completion_axis_row(
                    modulus, h_length, delta_length
                ) == h_length * (delta_length // modulus)
                assert additive_completion_axis_union(
                    modulus, h_length, delta_length
                ) == (
                    h_length * (delta_length // modulus)
                    + delta_length * (h_length // modulus)
                    - F(h_length * delta_length, modulus)
                )
    # In the balanced range H,L<s each complete axis is zero, so the
    # isolated (0,0) term is cancelled by the nonzero points on either axis.
    assert additive_completion_axis_row(11, 7, 5) == 0
    assert additive_completion_axis_union(11, 7, 5) == -F(35, 11)


def test_one_complete_axis_recombines_to_exact_residue_incidence() -> None:
    for modulus in range(2, 14):
        for shift in range(-modulus + 1, modulus):
            if gcd(shift, modulus) != 1:
                continue
            r = modulus + shift
            if r < 1:
                continue
            for h_length in range(1, 5):
                for delta_length in range(1, 5):
                    assert abs(
                        additive_completion_axis_recombined(
                            shift,
                            modulus,
                            h_length,
                            delta_length,
                        )
                        - additive_completion_shifted(
                            r, modulus, h_length, delta_length
                        )
                    ) < 1e-9


def test_balanced_short_dual_block_is_an_x_two_thirds_shift_gate() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert additive_shifted_chowla_ledger(box) == AdditiveShiftedChowlaLedger(
        h_frequency=F(1, 2),
        delta_frequency=F(1, 2),
        product_frequency=F(1),
        completion_amplitude=F(2),
        near_shift=F(2),
        near_trivial=F(8),
        local_target=F(6),
        required_saving=F(2),
        one_modulus_l2=F(17, 2),
        one_modulus_l2_gap=F(5, 2),
    )
    # With X=T^3 the critical shift length T^2 is X^(2/3).
    assert additive_shifted_chowla_ledger(box).near_shift / box.sigma == F(
        2, 3
    )
    assert (
        additive_shifted_chowla_ledger(
            boundary_witnesses()["large_q_endpoint"]
        ).one_modulus_l2
        is None
    )


def test_all_balanced_dual_blocks_have_at_most_the_same_near_gap() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    transition = additive_dual_block_ledger(box, F(1, 2), F(1, 2))
    assert transition == AdditiveDualBlockLedger(
        h_frequency=F(1, 2),
        delta_frequency=F(1, 2),
        h_fourier_amplitude=F(5, 2),
        delta_fourier_amplitude=F(5, 2),
        product_frequency=F(1),
        completion_amplitude=F(2),
        near_shift=F(2),
        near_trivial=F(8),
        local_target=F(6),
        required_saving=F(2),
        one_modulus_l2=F(17, 2),
        one_modulus_l2_gap=F(5, 2),
    )
    gaps = []
    for h_quarters in range(13):
        for delta_quarters in range(13):
            block = additive_dual_block_ledger(
                box, F(h_quarters, 4), F(delta_quarters, 4)
            )
            gaps.append(block.required_saving)
            assert block.required_saving <= 2
            if block.product_frequency >= box.sigma:
                assert block.required_saving == 0
    assert max(gaps) == 2


def test_shifted_product_phase_has_exact_scalar_gcd_denominator() -> None:
    for modulus in range(2, 30):
        for shift in range(-modulus + 1, modulus):
            if gcd(shift, modulus) != 1:
                continue
            for a in range(-6, 7):
                for b in range(-6, 7):
                    if a == 0 or b == 0:
                        continue
                    reduction = completed_product_phase_reduction(
                        shift, modulus, a, b
                    )
                    common = gcd(abs(a * b), modulus)
                    assert reduction == CompletedProductPhaseReduction(
                        scalar_gcd=common,
                        reduced_numerator=(
                            shift * (a * b // common)
                        )
                        % (modulus // common),
                        reduced_denominator=modulus // common,
                    )
                    assert gcd(
                        reduction.reduced_numerator,
                        reduction.reduced_denominator,
                    ) == 1
                    if abs(a * b) < modulus:
                        assert reduction.reduced_denominator * abs(
                            a * b
                        ) >= modulus


def test_scalar_gcd_does_not_remove_transition_block_resonance() -> None:
    reduction = completed_product_phase_reduction(-1, 62, 2, 2)
    assert reduction == CompletedProductPhaseReduction(
        scalar_gcd=2,
        reduced_numerator=29,
        reduced_denominator=31,
    )
    # The completed phase is -4/62=-2/31 and H=L=31, so (9.162)
    # survives inside a no-wrap transition block.
    assert abs(rectangular_product_kernel(31, 31, F(-2, 31)) - 31) < 1e-8


def test_squarefree_scalar_gcd_stratum_preserves_phase_and_mobius_sign() -> None:
    for modulus in range(2, 50):
        if naive_mobius(modulus) == 0:
            continue
        for a in range(-8, 9):
            for b in range(-8, 9):
                if a == 0 or b == 0:
                    continue
                stratum = squarefree_scalar_gcd_stratum(modulus, a, b)
                assert stratum == SquarefreeScalarGcdStratum(
                    a_gcd=gcd(abs(a), modulus),
                    b_gcd=gcd(
                        abs(b), modulus // gcd(abs(a), modulus)
                    ),
                    reduced_modulus=stratum.reduced_modulus,
                    a_reduced=a // gcd(abs(a), modulus),
                    b_reduced=b // stratum.b_gcd,
                    mobius_sign=naive_mobius(modulus),
                )
                assert stratum.a_gcd * stratum.b_gcd * (
                    stratum.reduced_modulus
                ) == modulus
                assert gcd(stratum.a_reduced, stratum.reduced_modulus) == 1
                assert gcd(stratum.b_reduced, stratum.reduced_modulus) == 1
                assert stratum.a_gcd * stratum.b_gcd == gcd(
                    abs(a * b), modulus
                )
                assert stratum.mobius_sign == (
                    naive_mobius(stratum.a_gcd)
                    * naive_mobius(stratum.b_gcd)
                    * naive_mobius(stratum.reduced_modulus)
                )
                assert F(a * b, modulus) % 1 == F(
                    stratum.a_reduced * stratum.b_reduced,
                    stratum.reduced_modulus,
                ) % 1


def test_squarefree_double_unit_sum_has_exact_divisor_spectrum() -> None:
    for modulus in range(1, 31):
        if naive_mobius(modulus) == 0:
            continue
        for d in range(1, modulus + 1):
            if gcd(d, modulus) != 1:
                continue
            for a_coefficient in range(-3, 4):
                for b_coefficient in range(-3, 4):
                    assert abs(
                        double_unit_bilinear_sum(
                            modulus,
                            a_coefficient,
                            b_coefficient,
                            d,
                        )
                        - double_unit_divisor_spectrum(
                            modulus,
                            a_coefficient,
                            b_coefficient,
                            d,
                        )
                    ) < 1e-8
                    assert abs(
                        naive_mobius(modulus)
                        * double_unit_bilinear_sum(
                            modulus,
                            a_coefficient,
                            b_coefficient,
                            d,
                        )
                        - mobius_weighted_double_unit_divisor_spectrum(
                            modulus,
                            a_coefficient,
                            b_coefficient,
                            d,
                        )
                    ) < 1e-8


def test_scalar_gcd_fourier_lifts_have_exact_q_modulus_formulas() -> None:
    for scalar in range(1, 8):
        for reduced_modulus in range(1, 9):
            if gcd(scalar, reduced_modulus) != 1:
                continue
            for residue in range(reduced_modulus):
                if gcd(residue, reduced_modulus) != 1:
                    continue
                for length in range(1, 10):
                    assert abs(
                        restricted_unit_fourier_lift(
                            scalar, reduced_modulus, residue, length
                        )
                        - restricted_unit_fourier_lift_formula(
                            scalar, reduced_modulus, residue, length
                        )
                    ) < 1e-8
                    assert abs(
                        unrestricted_fourier_lift(
                            scalar, reduced_modulus, residue, length
                        )
                        - unrestricted_fourier_lift_formula(
                            scalar, reduced_modulus, residue, length
                        )
                    ) < 1e-8


def test_complete_squarefree_scalar_stratum_has_migrated_divisor_spectrum() -> None:
    for a_gcd, b_gcd, reduced_modulus in (
        (1, 1, 2),
        (1, 1, 6),
        (1, 2, 3),
        (2, 1, 3),
        (2, 3, 5),
        (3, 2, 5),
    ):
        modulus = a_gcd * b_gcd * reduced_modulus
        for shift in range(1, modulus):
            if gcd(shift, modulus) != 1:
                continue
            for h_length in range(1, 5):
                for delta_length in range(1, 5):
                    assert abs(
                        squarefree_scalar_stratum_completed_sum(
                            a_gcd,
                            b_gcd,
                            reduced_modulus,
                            shift,
                            h_length,
                            delta_length,
                        )
                        - squarefree_scalar_stratum_divisor_spectrum(
                            a_gcd,
                            b_gcd,
                            reduced_modulus,
                            shift,
                            h_length,
                            delta_length,
                        )
                    ) < 1e-8


def test_scalar_stratum_coprimality_migration_has_exact_triple_spectrum() -> None:
    for a_gcd, b_gcd, reduced_modulus in (
        (1, 1, 6),
        (1, 1, 30),
        (1, 2, 3),
        (2, 1, 3),
        (2, 3, 5),
    ):
        modulus = a_gcd * b_gcd * reduced_modulus
        for shift in range(1, modulus):
            if gcd(shift, modulus) != 1:
                continue
            for h_length in range(1, 5):
                for delta_length in range(1, 6):
                    assert abs(
                        squarefree_scalar_stratum_divisor_spectrum(
                            a_gcd,
                            b_gcd,
                            reduced_modulus,
                            shift,
                            h_length,
                            delta_length,
                        )
                        - coprimality_migrated_scalar_stratum_spectrum(
                            a_gcd,
                            b_gcd,
                            reduced_modulus,
                            shift,
                            h_length,
                            delta_length,
                        )
                    ) < 1e-8


def test_bettin_chandee_bridge_still_misses_balanced_primitive_corner() -> None:
    ledger = scalar_stratum_bettin_chandee_ledger(
        r_length=F(3),
        scalar_a_gcd=F(1, 2),
        delta_gcd_factor=F(0),
        ramanujan_factor=F(0),
        oscillatory_modulus=F(5, 2),
        h_length=F(5, 2),
        delta_length=F(5, 2),
        scalar_b_gcd=F(0),
    )
    assert ledger == KloostermanFractionTripleLedger(
        product_length=F(9, 2),
        coefficient_norms=F(5),
        first_parenthesis=F(17, 4),
        second_parenthesis=F(75, 16),
        phase_penalty=F(0),
        fixed_factor_cost=F(1, 2),
        theorem_bound=F(163, 16),
        trivial_bound=F(21, 2),
        local_target=F(6),
        theorem_gap=F(67, 16),
        theorem_saving=F(5, 16),
    )


def test_ramanujan_weight_is_present_in_nonprimitive_coefficient_norm() -> None:
    ledger = scalar_stratum_bettin_chandee_ledger(
        r_length=F(3),
        scalar_a_gcd=F(1, 2),
        delta_gcd_factor=F(0),
        ramanujan_factor=F(1, 2),
        oscillatory_modulus=F(2),
        h_length=F(5, 2),
        delta_length=F(5, 2),
        scalar_b_gcd=F(0),
    )
    # The raw r, lambda and h*delta0 supports contribute 19/4; the
    # second moment of c_n(h) supplies the remaining n^(1/2)=T^(1/4).
    assert ledger.coefficient_norms == F(5)


def test_squarefree_ramanujan_period_has_exact_first_and_second_moments() -> None:
    for modulus in range(1, 50):
        if naive_mobius(modulus) == 0:
            continue
        phi = sum(1 for value in range(modulus) if gcd(value, modulus) == 1)
        prime_count = sum(
            1
            for prime in range(2, modulus + 1)
            if modulus % prime == 0
            and all(prime % divisor for divisor in range(2, prime))
        )
        values = [ramanujan_sum(modulus, h) for h in range(modulus)]
        assert sum(abs(value) for value in values) == 2**prime_count * phi
        assert sum(value * value for value in values) == modulus * phi


def test_bettin_chandee_covers_no_balanced_scalar_factor_box() -> None:
    assert balanced_scalar_stratum_bettin_chandee_uniform_gap() == F(2)
    grid = [F(index, 4) for index in range(13)]
    for a_gcd in grid:
        for b_gcd in grid:
            for delta_gcd in grid:
                for ramanujan_factor in grid:
                    oscillatory_modulus = (
                        F(3)
                        - a_gcd
                        - b_gcd
                        - delta_gcd
                        - ramanujan_factor
                    )
                    if oscillatory_modulus < 0:
                        continue
                    if b_gcd + ramanujan_factor > F(5, 2):
                        continue
                    ledger = scalar_stratum_bettin_chandee_ledger(
                        r_length=F(3),
                        scalar_a_gcd=a_gcd,
                        delta_gcd_factor=delta_gcd,
                        ramanujan_factor=ramanujan_factor,
                        oscillatory_modulus=oscillatory_modulus,
                        h_length=F(5, 2),
                        delta_length=F(5, 2),
                        scalar_b_gcd=b_gcd,
                    )
                    assert ledger.theorem_gap >= F(2)


def test_centered_inverse_cross_correlation_has_exact_lcm_formula() -> None:
    # For equal prime moduli and equal unit numerators the centered
    # variance is c_3(0)-c_3(1)^2/phi(3)=2-1/2=3/2.
    assert centered_inverse_cross_correlation_formula(3, 1, 3, 1) == F(3, 2)
    assert abs(centered_inverse_cross_correlation(3, 1, 3, 1) - 1.5) < 1e-9

    for left_modulus in range(1, 31):
        if naive_mobius(left_modulus) == 0:
            continue
        for right_modulus in range(1, 31):
            if naive_mobius(right_modulus) == 0:
                continue
            for left_numerator in range(-2, 4):
                for right_numerator in range(-2, 4):
                    direct = centered_inverse_cross_correlation(
                        left_modulus,
                        left_numerator,
                        right_modulus,
                        right_numerator,
                    )
                    closed = centered_inverse_cross_correlation_formula(
                        left_modulus,
                        left_numerator,
                        right_modulus,
                        right_numerator,
                    )
                    assert abs(direct - float(closed)) < 1e-8


def test_centered_inverse_cross_correlation_collapses_to_common_divisor() -> None:
    # CRT independence makes the covariance vanish identically when the
    # two squarefree oscillatory moduli are coprime.
    assert centered_inverse_cross_correlation_gcd_formula(6, 1, 35, 2) == 0
    # m=3*2, n=3*5, A=B=1 leaves the common-modulus variance 3/2.
    assert centered_inverse_cross_correlation_gcd_formula(6, 1, 15, 1) == F(3, 2)

    for left_modulus in range(1, 43):
        if naive_mobius(left_modulus) == 0:
            continue
        for right_modulus in range(1, 43):
            if naive_mobius(right_modulus) == 0:
                continue
            for left_numerator in range(-2, 4):
                for right_numerator in range(-2, 4):
                    assert centered_inverse_cross_correlation_gcd_formula(
                        left_modulus,
                        left_numerator,
                        right_modulus,
                        right_numerator,
                    ) == centered_inverse_cross_correlation_formula(
                        left_modulus,
                        left_numerator,
                        right_modulus,
                        right_numerator,
                    )


def test_double_unit_spectrum_mean_is_centered_before_layer_bounds() -> None:
    for modulus in (2, 3, 5, 6, 10, 30):
        for a_coefficient in range(-2, 4):
            for b_coefficient in range(-2, 4):
                expected = mobius_weighted_double_unit_mean(
                    modulus,
                    a_coefficient,
                    b_coefficient,
                )
                direct = sum(
                    naive_mobius(modulus)
                    * double_unit_bilinear_sum(
                        modulus,
                        a_coefficient,
                        b_coefficient,
                        bilinear_coefficient,
                    )
                    for bilinear_coefficient in range(modulus)
                    if gcd(bilinear_coefficient, modulus) == 1
                )
                phi_modulus = sum(
                    1 for residue in range(modulus) if gcd(residue, modulus) == 1
                )
                assert abs(direct - phi_modulus * float(expected)) < 1e-8

                centered = sum(
                    mobius_weighted_double_unit_divisor_spectrum(
                        modulus,
                        a_coefficient,
                        b_coefficient,
                        bilinear_coefficient,
                    )
                    - expected
                    for bilinear_coefficient in range(modulus)
                    if gcd(bilinear_coefficient, modulus) == 1
                )
                assert abs(centered) < 1e-8


def test_centered_double_unit_divisor_spectrum_centers_each_layer() -> None:
    for modulus in (2, 3, 5, 6, 10, 30):
        for a_coefficient in range(-2, 4):
            for b_coefficient in range(-2, 4):
                mean = mobius_weighted_double_unit_mean(
                    modulus,
                    a_coefficient,
                    b_coefficient,
                )
                for bilinear_coefficient in range(modulus):
                    if gcd(bilinear_coefficient, modulus) != 1:
                        continue
                    assert abs(
                        mobius_weighted_centered_double_unit_divisor_spectrum(
                            modulus,
                            a_coefficient,
                            b_coefficient,
                            bilinear_coefficient,
                        )
                        - (
                            mobius_weighted_double_unit_divisor_spectrum(
                                modulus,
                                a_coefficient,
                                b_coefficient,
                                bilinear_coefficient,
                            )
                            - mean
                        )
                    ) < 1e-8


def test_centered_inverse_cross_fourier_is_four_kloosterman_combination() -> None:
    for left_modulus in range(1, 19):
        if naive_mobius(left_modulus) == 0:
            continue
        for right_modulus in range(1, 19):
            if naive_mobius(right_modulus) == 0:
                continue
            for left_numerator in range(-1, 3):
                for right_numerator in range(-1, 3):
                    for frequency in range(-2, 3):
                        direct = centered_inverse_cross_fourier(
                            left_modulus,
                            left_numerator,
                            right_modulus,
                            right_numerator,
                            frequency,
                        )
                        closed = centered_inverse_cross_fourier_formula(
                            left_modulus,
                            left_numerator,
                            right_modulus,
                            right_numerator,
                            frequency,
                        )
                        assert abs(direct - closed) < 1e-8
                    assert abs(
                        centered_inverse_cross_fourier_formula(
                            left_modulus,
                            left_numerator,
                            right_modulus,
                            right_numerator,
                            0,
                        )
                        - float(
                            centered_inverse_cross_correlation_formula(
                                left_modulus,
                                left_numerator,
                                right_modulus,
                                right_numerator,
                            )
                        )
                    ) < 1e-8


def test_large_common_divisor_pairs_have_exact_union_bound() -> None:
    for dyadic_scale in range(2, 31):
        values = range(dyadic_scale + 1, 2 * dyadic_scale + 1)
        for threshold in range(2, 2 * dyadic_scale + 2):
            actual = sum(
                1
                for left_modulus in values
                for right_modulus in values
                if gcd(left_modulus, right_modulus) >= threshold
            )
            upper = large_common_divisor_pair_bound(
                dyadic_scale,
                threshold,
            )
            assert actual <= upper
            assert F(upper) <= F(
                4 * dyadic_scale * dyadic_scale,
                threshold - 1,
            )


def test_coprime_centered_cross_fourier_tensor_factorization() -> None:
    assert abs(centered_kloosterman_transform(1, 7, -3)) < 1e-9
    for left_modulus in range(1, 24):
        if naive_mobius(left_modulus) == 0:
            continue
        for right_modulus in range(1, 24):
            if (
                naive_mobius(right_modulus) == 0
                or gcd(left_modulus, right_modulus) != 1
            ):
                continue
            for left_numerator in range(-1, 3):
                for right_numerator in range(-1, 3):
                    for frequency in range(-2, 3):
                        assert abs(
                            coprime_centered_inverse_cross_fourier_factorization(
                                left_modulus,
                                left_numerator,
                                right_modulus,
                                right_numerator,
                                frequency,
                            )
                            - centered_inverse_cross_fourier_formula(
                                left_modulus,
                                left_numerator,
                                right_modulus,
                                right_numerator,
                                frequency,
                            )
                        ) < 1e-8


def test_centered_kloosterman_transform_has_three_term_crt_expansion() -> None:
    for left_factor in range(1, 10):
        for right_factor in range(1, 10):
            if gcd(left_factor, right_factor) != 1:
                continue
            for inverse_numerator in range(-2, 4):
                for linear_frequency in range(-3, 4):
                    terms = centered_kloosterman_crt_terms(
                        left_factor,
                        right_factor,
                        inverse_numerator,
                        linear_frequency,
                    )
                    assert isinstance(terms, CenteredKloostermanCrtTerms)
                    assert abs(
                        terms.total
                        - centered_kloosterman_transform(
                            left_factor * right_factor,
                            inverse_numerator,
                            linear_frequency,
                        )
                    ) < 1e-8


def test_centered_numerator_fourier_has_unit_support_and_literal_value() -> None:
    value = centered_kloosterman_numerator_fourier_formula(5, 2, 1, 1)
    assert abs(value.real - (-2.7950849718747373)) < 1e-10
    assert abs(value.imag - 2.938926261462366) < 1e-10
    assert abs(
        centered_kloosterman_numerator_fourier_formula(5, 2, 1, 0)
    ) < 1e-10
    composite = centered_kloosterman_numerator_fourier_formula(6, 5, 1, 5)
    assert abs(composite.real) < 1e-10
    assert abs(composite.imag - 5.196152422706632) < 1e-10


def test_centered_numerator_fourier_formula_matches_complete_sum() -> None:
    for modulus in range(1, 13):
        for multiplier in range(1, modulus + 1):
            if gcd(multiplier, modulus) != 1:
                continue
            for linear_frequency in range(-2, 3):
                for dual_frequency in range(-2, modulus + 2):
                    direct = centered_kloosterman_numerator_fourier(
                        modulus,
                        multiplier,
                        linear_frequency,
                        dual_frequency,
                    )
                    formula = centered_kloosterman_numerator_fourier_formula(
                        modulus,
                        multiplier,
                        linear_frequency,
                        dual_frequency,
                    )
                    assert abs(direct - formula) < 1e-8
                    if gcd(dual_frequency, modulus) != 1:
                        assert abs(formula) < 1e-8


def test_factorwise_centered_numerator_fourier_has_only_unit_modes() -> None:
    for left_factor in range(1, 7):
        for right_factor in range(1, 7):
            modulus = left_factor * right_factor
            if gcd(left_factor, right_factor) != 1:
                continue
            for multiplier in range(1, modulus + 1):
                if gcd(multiplier, modulus) != 1:
                    continue
                for linear_frequency in range(-1, 3):
                    for dual_frequency in range(-1, modulus + 1):
                        direct = (
                            factorized_centered_kloosterman_numerator_fourier(
                                left_factor,
                                right_factor,
                                multiplier,
                                linear_frequency,
                                dual_frequency,
                            )
                        )
                        formula = (
                            factorized_centered_kloosterman_numerator_fourier_formula(
                                left_factor,
                                right_factor,
                                multiplier,
                                linear_frequency,
                                dual_frequency,
                            )
                        )
                        assert abs(direct - formula) < 1e-8
                        if gcd(dual_frequency, modulus) != 1:
                            assert abs(formula) < 1e-8


def test_dual_unit_reciprocity_combines_both_modular_phases() -> None:
    for left_modulus in range(2, 13):
        for right_modulus in range(2, 13):
            if gcd(left_modulus, right_modulus) != 1:
                continue
            for left_dual in range(1, 5):
                for right_dual in range(1, 5):
                    if (
                        gcd(left_dual, right_dual) != 1
                        or gcd(
                            left_modulus * right_modulus,
                            left_dual * right_dual,
                        )
                        != 1
                    ):
                        continue
                    for frequency in range(1, 3):
                        for left_numerator in range(1, 3):
                            for right_numerator in range(1, 3):
                                direct = dual_unit_reciprocity_phase(
                                    left_modulus,
                                    right_modulus,
                                    left_dual,
                                    right_dual,
                                    frequency,
                                    left_numerator,
                                    right_numerator,
                                )
                                formula = dual_unit_reciprocity_phase_formula(
                                    left_modulus,
                                    right_modulus,
                                    left_dual,
                                    right_dual,
                                    frequency,
                                    left_numerator,
                                    right_numerator,
                                )
                                assert abs(direct - formula) < 1e-8


def test_young_additive_rational_sieve_hits_exact_required_saving() -> None:
    assert young_dual_reciprocity_ledger(
        outer_modulus=F(5, 2),
        row_length=F(2),
        numerator_length=F(2),
        denominator_length=F(5, 2),
        required_saving=F(2),
    ) == YoungDualReciprocityLedger(
        rational_height=F(9, 2),
        large_sieve_constant=F(5),
        coefficient_energy=F(17, 2),
        row_cauchy=F(9, 4),
        theorem_bound=F(9),
        trivial_bound=F(11),
        saving=F(2),
        margin=F(0),
    )


def test_scalar_factor_cost_reopens_the_transition_corner() -> None:
    assert young_scalar_transition_ledger(
        r_length=F(3),
        total_modulus=F(3),
        scalar_fixed=F(1, 2),
        oscillatory_modulus=F(5, 2),
        h_length=F(5, 2),
        delta_length=F(5, 2),
        common_factor=F(0),
    ) == YoungScalarTransitionLedger(
        reduced_numerator=F(2),
        outer_modulus=F(5, 2),
        row_length=F(2),
        rational_height=F(9, 2),
        coefficient_energy=F(17, 2),
        row_cauchy=F(9, 4),
        large_sieve_constant=F(5),
        theorem_bound=F(19, 2),
        raw_bound=F(23, 2),
        second_moment_target=F(9),
        theorem_gap=F(1, 2),
        required_saving=F(5, 2),
        theorem_saving=F(2),
    )


def test_common_factor_covers_transition_exactly_from_one_quarter() -> None:
    for common_factor_quarters in range(9):
        common_factor = F(common_factor_quarters, 4)
        ledger = young_scalar_transition_ledger(
            r_length=F(3),
            total_modulus=F(3),
            scalar_fixed=F(1, 2),
            oscillatory_modulus=F(5, 2),
            h_length=F(5, 2),
            delta_length=F(5, 2),
            common_factor=common_factor,
        )
        assert ledger.theorem_bound == F(19, 2) - 2 * common_factor
        assert (ledger.theorem_gap <= 0) == (common_factor >= F(1, 4))


def test_centered_inverse_numerator_fourier_is_delta_minus_mean() -> None:
    for modulus in range(1, 13):
        for multiplier in range(modulus):
            for residue in range(modulus):
                if gcd(residue, modulus) != 1:
                    continue
                for dual_frequency in range(modulus):
                    direct = centered_inverse_numerator_fourier(
                        modulus,
                        multiplier,
                        residue,
                        dual_frequency,
                    )
                    formula = centered_inverse_numerator_fourier_formula(
                        modulus,
                        multiplier,
                        residue,
                        dual_frequency,
                    )
                    assert abs(direct - formula) < 1e-8


def test_common_modulus_centered_residue_collision_has_crt_formula() -> None:
    for common_factor in range(1, 6):
        for left_cofactor in range(1, 6):
            for right_cofactor in range(1, 6):
                if (
                    gcd(common_factor, left_cofactor) != 1
                    or gcd(common_factor, right_cofactor) != 1
                    or gcd(left_cofactor, right_cofactor) != 1
                ):
                    continue
                left_modulus = common_factor * left_cofactor
                right_modulus = common_factor * right_cofactor
                for left_residue in range(left_modulus):
                    if gcd(left_residue, left_modulus) != 1:
                        continue
                    for right_residue in range(right_modulus):
                        if gcd(right_residue, right_modulus) != 1:
                            continue
                        for frequency in range(-3, 4):
                            direct = centered_residue_collision_fourier(
                                left_modulus,
                                right_modulus,
                                left_residue,
                                right_residue,
                                frequency,
                            )
                            formula = centered_residue_collision_fourier_formula(
                                left_modulus,
                                right_modulus,
                                left_residue,
                                right_residue,
                                frequency,
                            )
                            assert abs(direct - formula) < 1e-8


def test_nonunit_reduced_collision_only_adds_a_free_ramanujan_factor() -> None:
    for ambient_modulus in range(1, 21):
        if naive_mobius(ambient_modulus) == 0:
            continue
        ambient_divisors = [
            divisor
            for divisor in range(1, ambient_modulus + 1)
            if ambient_modulus % divisor == 0
        ]
        for left_modulus in ambient_divisors:
            for right_modulus in ambient_divisors:
                for left_residue in range(left_modulus):
                    if gcd(left_residue, left_modulus) != 1:
                        continue
                    for right_residue in range(right_modulus):
                        if gcd(right_residue, right_modulus) != 1:
                            continue
                        for frequency in range(-3, 4):
                            direct = ambient_centered_residue_collision_fourier(
                                ambient_modulus,
                                left_modulus,
                                right_modulus,
                                left_residue,
                                right_residue,
                                frequency,
                            )
                            formula = (
                                ambient_centered_residue_collision_fourier_formula(
                                    ambient_modulus,
                                    left_modulus,
                                    right_modulus,
                                    left_residue,
                                    right_residue,
                                    frequency,
                                )
                            )
                            assert abs(direct - formula) < 1e-8


def test_common_modulus_zero_mode_is_a_centered_t_congruence() -> None:
    for common_factor in range(1, 10):
        for left_cofactor in range(1, 6):
            for right_cofactor in range(1, 6):
                if (
                    gcd(common_factor, left_cofactor) != 1
                    or gcd(common_factor, right_cofactor) != 1
                    or gcd(left_cofactor, right_cofactor) != 1
                ):
                    continue
                left_modulus = common_factor * left_cofactor
                right_modulus = common_factor * right_cofactor
                for left_residue in range(left_modulus):
                    if gcd(left_residue, left_modulus) != 1:
                        continue
                    for right_residue in range(right_modulus):
                        if gcd(right_residue, right_modulus) != 1:
                            continue
                        formula = centered_residue_collision_fourier_formula(
                            left_modulus,
                            right_modulus,
                            left_residue,
                            right_residue,
                            0,
                        )
                        zero_formula = centered_residue_collision_zero_formula(
                            common_factor,
                            left_residue,
                            right_residue,
                        )
                        assert abs(formula - float(zero_formula)) < 1e-8


def test_centered_unit_congruence_has_only_interval_boundary_error() -> None:
    for modulus in range(1, 25):
        for left_length in range(1, 18):
            for right_length in range(1, 18):
                for left_multiplier in range(1, min(modulus + 1, 6)):
                    if gcd(left_multiplier, modulus) != 1:
                        continue
                    for right_multiplier in range(1, min(modulus + 1, 6)):
                        if gcd(right_multiplier, modulus) != 1:
                            continue
                        centered_sum = centered_unit_congruence_sum(
                            modulus,
                            left_length,
                            right_length,
                            left_multiplier,
                            right_multiplier,
                        )
                        assert abs(centered_sum) <= (
                            centered_unit_congruence_boundary_majorant(
                                modulus,
                                left_length,
                            )
                        )


def test_young_dual_gcd_strata_never_exceed_the_target() -> None:
    assert young_dual_reciprocity_gcd_ledger(F(0), F(0)) == (
        YoungDualGcdLedger(
            reduced_outer_modulus=F(5, 2),
            reduced_row_length=F(2),
            rational_height=F(9, 2),
            large_sieve_constant=F(5),
            coefficient_energy=F(17, 2),
            theorem_bound=F(9),
            target=F(9),
            margin=F(0),
        )
    )
    assert young_dual_reciprocity_gcd_ledger(F(1, 2), F(0)).margin == F(
        1, 4
    )
    assert young_dual_reciprocity_gcd_ledger(F(0), F(1, 2)).margin == F(
        1, 4
    )
    assert young_dual_reciprocity_gcd_ledger(
        F(0), F(0), F(1, 2)
    ).margin == F(0)
    for kappa_quarters in range(9):
        for eta_quarters in range(9):
            if kappa_quarters + eta_quarters > 10:
                continue
            for rational_gcd_quarters in range(9 - eta_quarters):
                ledger = young_dual_reciprocity_gcd_ledger(
                    F(kappa_quarters, 4),
                    F(eta_quarters, 4),
                    F(rational_gcd_quarters, 4),
                )
                assert ledger.theorem_bound <= ledger.target


def test_young_common_factor_collision_gains_two_powers_of_t() -> None:
    assert young_common_factor_ledger(F(0)) == YoungCommonFactorLedger(
        outer_modulus=F(5, 2),
        row_length=F(2),
        rational_height=F(9, 2),
        coefficient_energy=F(17, 2),
        large_sieve_constant=F(5),
        fixed_common_factor_bound=F(9),
        summed_bound=F(9),
        target=F(9),
        margin=F(0),
    )
    for common_factor_quarters in range(9):
        common_factor = F(common_factor_quarters, 4)
        ledger = young_common_factor_ledger(common_factor)
        assert ledger.fixed_common_factor_bound == F(9) - 3 * common_factor
        assert ledger.summed_bound == F(9) - 2 * common_factor
        assert ledger.summed_bound <= ledger.target
        numerator_length_quarters = 8 - common_factor_quarters
        row_length_quarters = numerator_length_quarters
        outer_length_quarters = 10 - common_factor_quarters
        for row_gcd_quarters in range(row_length_quarters + 1):
            for numerator_gcd_quarters in range(
                numerator_length_quarters + 1
            ):
                if (
                    row_gcd_quarters + numerator_gcd_quarters
                    > outer_length_quarters
                ):
                    continue
                for rational_gcd_quarters in range(
                    numerator_length_quarters
                    - numerator_gcd_quarters
                    + 1
                ):
                    stratified = young_common_factor_ledger(
                        common_factor,
                        F(row_gcd_quarters, 4),
                        F(numerator_gcd_quarters, 4),
                        F(rational_gcd_quarters, 4),
                    )
                    assert stratified.summed_bound <= stratified.target


def test_common_factor_ramanujan_marginals_are_below_target() -> None:
    assert common_factor_marginal_ledger(F(0)) == (
        CommonFactorMarginalLedger(
            one_sided_bound=F(17, 2),
            all_mean_bound=F(6),
            target=F(9),
            one_sided_margin=F(1, 2),
            all_mean_margin=F(3),
        )
    )
    for common_factor_quarters in range(9):
        ledger = common_factor_marginal_ledger(
            F(common_factor_quarters, 4)
        )
        assert ledger.one_sided_bound <= ledger.target
        assert ledger.all_mean_bound <= ledger.target


def test_linear_convolution_energy_loses_a_rational_gcd_factor() -> None:
    for left_length in range(1, 9):
        for right_length in range(1, 9):
            for left_multiplier in range(1, 5):
                for right_multiplier in range(1, 5):
                    for divisor in range(1, right_length + 1):
                        if gcd(right_multiplier, divisor) != 1:
                            continue
                        assert linear_convolution_energy_on_multiples(
                            left_length,
                            right_length,
                            left_multiplier,
                            right_multiplier,
                            divisor,
                        ) <= linear_convolution_energy_on_multiples_majorant(
                            left_length,
                            right_length,
                            divisor,
                        )


def test_squarefree_ramanujan_means_collapse_to_the_coprime_cofactor() -> None:
    for modulus in range(1, 80):
        if naive_mobius(modulus) == 0:
            continue
        for frequency in range(-20, 21):
            ramanujan_sum = sum(
                divisor * naive_mobius(modulus // divisor)
                for divisor in range(1, modulus + 1)
                if modulus % divisor == 0 and frequency % divisor == 0
            )
            actual = F(
                ramanujan_sum,
                sum(1 for residue in range(modulus) if gcd(residue, modulus) == 1),
            )
            assert actual == squarefree_normalized_ramanujan_mean_formula(
                modulus,
                frequency,
            )


def test_dyadic_ramanujan_mean_sum_has_finite_divisor_majorant() -> None:
    for scale in range(1, 25):
        for frequency in range(1, 40):
            assert ramanujan_mean_dyadic_sum(
                scale,
                frequency,
            ) <= ramanujan_mean_dyadic_divisor_majorant(
                scale,
                frequency,
            )


def test_two_sided_centered_crt_tensor_has_exactly_nine_terms() -> None:
    factor_pairs = ((1, 1), (1, 2), (2, 3), (3, 5), (5, 7))
    for left_short, left_long in factor_pairs:
        left_modulus = left_short * left_long
        for right_short, right_long in factor_pairs:
            right_modulus = right_short * right_long
            if gcd(left_modulus, right_modulus) != 1:
                continue
            for left_numerator in range(-1, 2):
                for right_numerator in range(-1, 2):
                    for frequency in range(-2, 3):
                        terms = two_sided_centered_kloosterman_crt_terms(
                            left_short,
                            left_long,
                            left_numerator,
                            right_short,
                            right_long,
                            right_numerator,
                            frequency,
                        )
                        assert len(terms) == 9
                        assert abs(
                            sum(terms)
                            - centered_inverse_cross_fourier_formula(
                                left_modulus,
                                left_numerator,
                                right_modulus,
                                right_numerator,
                                frequency,
                            )
                        ) < 1e-8
                        if frequency == 0:
                            assert abs(sum(terms)) < 1e-8


def test_balanced_unit_crt_mean_terms_have_exact_savings_ledger() -> None:
    assert centered_crt_unit_mean_ledger(
        local_factor_exponent=F(5, 4),
        required_saving=F(2),
    ) == CenteredCrtUnitMeanLedger(
        saving_per_mean=F(15, 8),
        one_mean_gap=F(1, 8),
        two_mean_margin=F(7, 4),
    )


def test_blomer_pascadi_unbalanced_tensor_insertions_are_still_trivial() -> None:
    long_short = blomer_pascadi_unbalanced_ledger(F(4, 5), F(1))
    assert long_short == BlomerPascadiUnbalancedLedger(
        first_term=F(1, 10),
        second_term=F(1, 20),
        third_term=F(2, 15),
        fourth_term=F(11, 45),
        fifth_term=F(0),
        saving_factor=F(11, 45),
        best_trivial_factor=F(1),
        theorem_factor=F(56, 45),
        theorem_gap=F(11, 45),
    )
    short_short = blomer_pascadi_unbalanced_ledger(F(4, 5), F(4, 5))
    assert short_short.saving_factor == F(13, 90)
    assert short_short.best_trivial_factor == F(1)
    assert short_short.theorem_gap == F(13, 90)


def test_pascadi_2024_direct_dispersion_bound_is_too_large() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert pascadi_2024_direct_dispersion_gap(box) == F(11, 2)


def test_research_note_contains_no_embedded_control_characters() -> None:
    note = (
        Path(__file__).parents[1]
        / "docs/research/2026-08-24-mobius-weighted-off-diagonal.md"
    ).read_bytes()
    forbidden = {
        byte
        for byte in note
        if byte < 32 and byte not in {ord("\n"), ord("\t")}
    }
    assert forbidden == set()
