import sys
from fractions import Fraction as F
from math import gcd
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts import mwkf_mobius_type_identity as type_identity
from scripts.audit_mwkf_coverage import (
    wright_denominator_factor_adapter,
    wright_type_i_adapter,
)
from scripts.audit_mwkf_ranges import boundary_witnesses
from scripts.mwkf_mobius_type_identity import (
    bilinear_gauss_via_orthogonality,
    c_u,
    centered_completion_via_orthogonality,
    centered_product_frequency_coefficients,
    centered_selberg_product_boundary_sides,
    coprime_divisor_pair_identity,
    crt_reciprocity_numerators,
    determinant_cokernel_coordinates,
    determinant_lattice_solution,
    determinant_line_coordinates,
    determinant_line_coprimality_indicator,
    determinant_line_coprimality_residue,
    determinant_slope_square_coordinates,
    double_centered_completion_via_orthogonality,
    double_split_mobius_identity,
    endpoint_density_convolution_coefficient,
    endpoint_q_density,
    endpoint_weighted_mobius,
    mobius,
    poisson_congruence_reparametrization,
    product_lift_coefficients,
    product_lift_shifted_correlation,
    q_free_part,
    q_restricted_mobius_log_signature,
    q_restricted_twisted_log_signature,
    signed_shift_solutions,
    split_mobius_identity,
    truncated_selberg_divisor_sides,
    type_scale_bounds,
    zeta_mollifier_pairing_sides,
)

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


def test_long_cutoff_coefficient_reflects_to_short_divisors() -> None:
    """On squarefree support, c_U(a) is -mu(a) times the reflected sum."""
    for a in range(2, 120):
        if mobius(a) == 0:
            continue
        for cutoff in range(1, a):
            reflected = sum(
                mobius(e)
                for e in type_identity.divisors(a)
                if e * cutoff < a
            )
            assert c_u(a, cutoff) == -mobius(a) * reflected


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


def test_coupled_double_split_preserves_product_phase_and_two_mobius_sides() -> None:
    adapter = getattr(
        type_identity,
        "coupled_product_double_mobius_certificate",
        None,
    )
    assert adapter is not None, "coupled double-Mobius certificate is missing"

    certificate = adapter(
        r=30,
        s=77,
        h=3,
        delta=-5,
        r_cutoff_u=3,
        r_cutoff_v=5,
        s_cutoff_u=4,
        s_cutoff_v=6,
    )

    assert certificate.direct_mobius_product == mobius(30) * mobius(77)
    assert sum(dict(certificate.sector_sums).values()) == (
        certificate.direct_mobius_product
    )
    assert {name for name, _ in certificate.sector_sums} == {
        "I/I",
        "I/II",
        "II/I",
        "II/II",
    }
    assert certificate.product_frequency == -15
    assert certificate.phase_mod_one == F(39, 77)
    assert certificate.poisson_frequency is None
    assert certificate.poisson_product is None
    assert certificate.poisson_phase_mod_one is None
    assert certificate.product_frequency_preserved
    assert certificate.poisson_product_preserved
    assert certificate.both_reciprocal_phases_preserved
    assert certificate.two_mobius_sides_preserved
    assert certificate.recombination_identity_verified

    for term in certificate.terms:
        assert term.r_long_factor * term.r_short_mobius_factor == 30
        assert term.s_long_factor * term.s_short_mobius_factor == 77
        assert term.product_frequency == certificate.product_frequency
        assert term.phase_mod_one == certificate.phase_mod_one
        assert term.coefficient == (
            term.r_truncated_coefficient
            * term.r_short_mobius_value
            * term.s_truncated_coefficient
            * term.s_short_mobius_value
        )


def test_coupled_double_split_can_retain_the_second_bblr_product_phase() -> None:
    certificate = type_identity.coupled_product_double_mobius_certificate(
        r=30,
        s=77,
        h=3,
        delta=-5,
        poisson_frequency=7,
        r_cutoff_u=3,
        r_cutoff_v=5,
        s_cutoff_u=4,
        s_cutoff_v=6,
    )

    assert certificate.product_frequency == -15
    assert certificate.poisson_frequency == 7
    assert certificate.poisson_product == 21
    assert certificate.poisson_phase_mod_one == F(1, 11)
    assert certificate.phase_mod_one == F(39, 77)
    assert certificate.product_frequency_preserved
    assert certificate.poisson_product_preserved
    assert certificate.both_reciprocal_phases_preserved
    for term in certificate.terms:
        assert term.product_frequency == -15
        assert term.phase_mod_one == F(39, 77)
        assert term.poisson_frequency == 7
        assert term.poisson_product == 21
        assert term.poisson_phase_mod_one == F(1, 11)

    with pytest.raises(ValueError, match="requires l nonzero"):
        type_identity.coupled_product_double_mobius_certificate(
            r=30,
            s=77,
            h=3,
            delta=-5,
            poisson_frequency=0,
            r_cutoff_u=3,
            r_cutoff_v=5,
            s_cutoff_u=4,
            s_cutoff_v=6,
        )


def test_double_quotient_factorization_matches_drappeau_phase_exactly() -> None:
    adapter = getattr(
        type_identity,
        "drappeau_double_quotient_phase",
        None,
    )
    assert adapter is not None, "Drappeau double-quotient phase is missing"

    phase = adapter(
        numerator=15,
        r_short=2,
        r_truncated_divisor=3,
        r_smooth_quotient=5,
        s_short=7,
        s_truncated_divisor=1,
        s_smooth_quotient=11,
    )

    assert phase.original_r == 30
    assert phase.original_s == 77
    assert phase.drappeau_r == 6
    assert phase.drappeau_d == 5
    assert phase.drappeau_s == 7
    assert phase.drappeau_c == 11
    assert phase.drappeau_n == -15
    assert phase.original_phase == F(38, 77)
    assert phase.drappeau_phase == F(38, 77)
    assert phase.phase_identity_verified
    assert phase.coprimality_identity_verified


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


def test_pure_unsigned_mobius_sector_is_exactly_minus_one() -> None:
    """Catch estimating the zero-outer BBLR cell before recombination."""
    adapter = getattr(
        type_identity,
        "mobius_unsigned_sector_recombination",
        None,
    )
    assert adapter is not None, "unsigned-sector recombination helper is missing"

    for n, cutoff in ((30, 5), (210, 10), (2310, 20)):
        audit = adapter(n=n, cutoff_u=cutoff)
        assert audit.mobius_value == mobius(n)
        assert audit.pure_unsigned_outer_product == 1
        assert audit.pure_unsigned_contribution == -1
        assert audit.nontrivial_signed_contribution == mobius(n) + 1
        assert audit.recombined_contribution == mobius(n)
        assert sum(value for _, value in audit.outer_contributions) == mobius(n)
        assert audit.recombination_identity_verified


def test_bblr_outer_product_weight_is_not_a_parent_free_coefficient() -> None:
    """The same BBLR outer index retains its parent/inner-factor history."""
    adapter = getattr(
        type_identity,
        "bblr_coefficient_stage_separation_witness",
        None,
    )
    assert adapter is not None, "BBLR coefficient-stage witness is missing"

    audit = adapter(
        cutoff_u=3,
        shared_outer_product=2,
        left_parent=6,
        right_parent=10,
    )

    assert audit.left_outer_contribution == 1
    assert audit.right_outer_contribution == 2
    assert audit.same_outer_product
    assert audit.parent_dependent_outer_weight
    assert audit.direct_outer_index_only_adapter_refuted
    assert audit.packet_exhaustive_parent_aware_adapter_still_open


def test_bblr_common_unsigned_cofactor_is_an_exact_gcd_gram_kernel() -> None:
    helper = getattr(
        type_identity,
        "bblr_common_unsigned_cofactor_gram_sides",
        None,
    )
    assert helper is not None, "BBLR common-cofactor Gram helper is missing"

    sides = helper(
        cutoff_u=3,
        left_parent_weights={10: F(2)},
        right_parent_weights={15: F(3)},
    )

    # C_3(10;2)=C_3(15;3)=2 and both have inner quotient r=5.
    assert sides.direct_partial_diagonal_sum == F(24)
    assert sides.gcd_kernel_sum == F(24)
    assert sides.common_cofactor_gram_sum == F(24)
    assert sides.active_common_cofactor_rows == ((5, F(4), F(6)),)
    assert sides.direct_to_gcd_kernel_identity_verified
    assert sides.gcd_kernel_to_gram_identity_verified
    assert sides.parent_and_inner_quotient_retained
    assert not sides.analytic_bblr_packet_exhaustive
    assert not sides.target_bound_proved

    square = helper(
        cutoff_u=3,
        left_parent_weights={10: F(2), 15: F(3)},
        right_parent_weights={10: F(2), 15: F(3)},
    )
    assert all(left == right for _, left, right in square.active_common_cofactor_rows)
    assert square.common_cofactor_gram_sum == sum(
        left * left for _, left, _ in square.active_common_cofactor_rows
    )


def test_bblr_four_parent_partial_diagonal_recombines_two_mobius_factors() -> None:
    helper = getattr(
        type_identity,
        "bblr_four_parent_partial_diagonal_sides",
        None,
    )
    assert helper is not None, "BBLR four-parent partial diagonal is missing"

    sides = helper(
        parent_cutoffs=(3, 3, 3, 3),
        labelled_parent_kernels={
            "dual/slot-1": {(10, 15, 6, 10): F(-1)},
            "main/slot-2": {(6, 10, 14, 15): F(2)},
        },
    )

    # P_3(10,15)=P_3(15,10)=4 and the unconstrained parents have mu=1.
    assert sides.direct_four_type_sum == F(4)
    assert sides.recombined_two_parent_sum == F(4)
    assert sides.gcd_kernel_sum == F(4)
    assert sides.labelled_recombined_sums == (
        ("dual/slot-1", F(-4)),
        ("main/slot-2", F(8)),
    )
    assert sides.direct_to_two_parent_recombination_verified
    assert sides.two_parent_to_gcd_kernel_verified
    assert sides.unconstrained_parent_type_sums_recombined_to_mobius
    assert sides.common_diagonal_parent_kernel_retained
    assert sides.supplied_slot_order_labels_retained == (
        "dual/slot-1",
        "main/slot-2",
    )
    assert not sides.analytic_afe_packet_exhaustive
    assert not sides.target_bound_proved

    asymmetric = helper(
        parent_cutoffs=(2, 5, 3, 3),
        labelled_parent_kernels={
            "main/asymmetric-cutoff": {(6, 10, 14, 15): F(2)},
        },
    )
    # C_5(10;2)=1 while C_3(15;3)=2 at their common quotient 5.
    assert asymmetric.direct_four_type_sum == F(4)
    assert asymmetric.recombined_two_parent_sum == F(4)
    assert asymmetric.gcd_kernel_sum == F(4)
    assert asymmetric.direct_to_two_parent_recombination_verified
    assert asymmetric.two_parent_to_gcd_kernel_verified


def test_four_mobius_pure_unsigned_bblr_box_has_positive_unit_weight() -> None:
    """The worst BBLR box loses every Möbius sign before global recombination."""
    adapter = getattr(
        type_identity,
        "four_mobius_unsigned_sector_recombination",
        None,
    )
    assert adapter is not None, "four-Möbius recombination helper is missing"

    audit = adapter(values=(30, 6, 10, 14), cutoff_u=5)
    assert audit.recombined_mobius_product == -1
    assert audit.pure_unsigned_bblr_box_contribution == 1
    assert audit.all_other_boxes_contribution == -2
    assert audit.pure_box_is_unweighted_and_positive
    assert audit.recombination_identity_verified


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


def test_common_b_phase_keeps_nonzero_determinants_without_divisibility() -> None:
    """Catch imposing b|Delta before a completion has produced that mode."""
    adapter = getattr(
        type_identity,
        "common_b_phase_reciprocity",
        None,
    )
    assert adapter is not None, "common-b phase reciprocity helper is missing"

    generic = adapter(n1=13, y1=6, n2=17, y2=35, b=11)
    assert generic.determinant == 353
    assert not generic.b_divides_determinant
    assert generic.original_phase == generic.determinant_phase
    assert generic.original_phase == generic.reciprocal_completed_phase

    zero_completion_mode = adapter(n1=3, y1=6, n2=1, y2=35, b=11)
    assert zero_completion_mode.determinant == 99
    assert zero_completion_mode.b_divides_determinant
    assert zero_completion_mode.original_phase == F(0)


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


def test_determinant_line_coordinates_exhaust_every_bounded_solution() -> None:
    """Catch losing a gcd layer or reversing the primitive line steps."""
    for j, v, delta in ((6, 15, 21), (-6, 15, 21), (10, -14, -22)):
        coordinates = determinant_line_coordinates(j=j, v=v, delta=delta)
        assert coordinates.gcd_j_v == gcd(abs(j), abs(v))
        assert coordinates.gcd_j_v * coordinates.primitive_j == j
        assert coordinates.gcd_j_v * coordinates.primitive_v == v
        assert coordinates.gcd_j_v * coordinates.shift_quotient == delta
        assert gcd(abs(coordinates.primitive_j), abs(coordinates.primitive_v)) == 1

        line_solutions = {
            coordinates.solution(n) for n in range(-100, 101)
        }
        brute_solutions = {
            (r, s)
            for r in range(-30, 31)
            for s in range(-30, 31)
            if r * v - j * s == delta
        }
        assert brute_solutions <= line_solutions
        for r, s in line_solutions:
            assert r * v - j * s == delta


def test_determinant_line_coprimality_is_exact_shift_divisor_inversion() -> None:
    """Catch omitting the unique n-residue attached to d|delta0."""
    coordinates = determinant_line_coordinates(j=6, v=15, delta=21)
    for divisor in (1, 7):
        residue = determinant_line_coprimality_residue(
            coordinates,
            divisor=divisor,
        )
        hits = [
            n
            for n in range(divisor)
            if all(value % divisor == 0 for value in coordinates.solution(n))
        ]
        assert hits == [residue]

    for n in range(-100, 101):
        r, s = coordinates.solution(n)
        assert determinant_line_coprimality_indicator(coordinates, n=n) == (
            1 if gcd(abs(r), abs(s)) == 1 else 0
        )


def test_slope_square_cross_determinant_recovers_the_common_primitive_slope() -> None:
    """Verify the exact Cramer formulas in the EDSSF off-diagonal."""
    for r1, s1, r2, s2, j, v in (
        (5, 7, 8, 11, 2, 3),
        (7, 9, 11, 13, -3, 4),
        (8, 11, 13, 17, 5, -2),
    ):
        audit = determinant_slope_square_coordinates(
            r1=r1,
            s1=s1,
            r2=r2,
            s2=s2,
            primitive_j=j,
            primitive_v=v,
        )
        assert audit.cross_determinant == r1 * s2 - r2 * s1
        assert audit.shift1 == r1 * v - s1 * j
        assert audit.shift2 == r2 * v - s2 * j
        assert audit.cross_determinant != 0
        assert audit.recovered_primitive_j == j
        assert audit.recovered_primitive_v == v
        assert not audit.zero_determinant_is_identity_diagonal


def test_zero_cross_determinant_is_exactly_the_primitive_identity_diagonal() -> None:
    """Catch retaining proportional but distinct primitive (r,s) pairs."""
    audit = determinant_slope_square_coordinates(
        r1=5,
        s1=7,
        r2=5,
        s2=7,
        primitive_j=2,
        primitive_v=3,
    )
    assert audit.cross_determinant == 0
    assert audit.zero_determinant_is_identity_diagonal
    assert audit.recovered_primitive_j is None
    assert audit.recovered_primitive_v is None


def test_primitive_cross_determinant_cokernel_has_only_delta_characters() -> None:
    """The two Cramer divisibilities have joint index |Delta|, not Delta^2."""
    for r1, s1, r2, s2 in (
        (1, 2, 3, 1),
        (1, 1, 1, 7),
        (2, 5, 7, 3),
    ):
        audit = determinant_cokernel_coordinates(
            r1=r1,
            s1=s1,
            r2=r2,
            s2=s2,
        )
        modulus = abs(r1 * s2 - r2 * s1)
        assert audit.modulus == modulus
        assert audit.smith_first_invariant == 1
        assert audit.smith_second_invariant == modulus
        assert audit.cokernel_is_cyclic
        assert len(audit.admissible_shift_residues) == modulus
        assert len(audit.annihilator_characters) == modulus

        admissible = set(audit.admissible_shift_residues)
        annihilator = audit.annihilator_characters
        for delta1 in range(modulus):
            for delta2 in range(modulus):
                phases = tuple(
                    (a * delta1 + b * delta2) % modulus
                    for a, b in annihilator
                )
                if (delta1, delta2) in admissible:
                    assert phases == (0,) * modulus
                else:
                    # Exact finite-character orthogonality: every residue
                    # in the image of this nontrivial character has the
                    # same multiplicity, so its root-of-unity sum is zero.
                    image = sorted(set(phases))
                    multiplicities = {phases.count(value) for value in image}
                    assert len(multiplicities) == 1
                    assert len(image) > 1


def test_determinant_cokernel_rejects_nonprimitive_rows() -> None:
    with pytest.raises(ValueError, match="primitive determinant rows"):
        determinant_cokernel_coordinates(r1=2, s1=4, r2=1, s2=3)


def test_endpoint_q_density_turns_restricted_mobius_into_fixed_convolution() -> None:
    """Verify f=mu*h for g(n)=prod_(p|n)(1+1/p)^(-1)."""
    for n in range(1, 300):
        convolution = sum(
            F(mobius(n // divisor))
            * endpoint_density_convolution_coefficient(divisor)
            for divisor in type_identity.divisors(n)
        )
        assert convolution == endpoint_weighted_mobius(n)

    for prime in (2, 3, 5, 7, 11, 13):
        assert endpoint_q_density(prime) == F(prime, prime + 1)
        for exponent in (1, 2, 3):
            assert endpoint_density_convolution_coefficient(
                prime**exponent
            ) == F(1, prime + 1)


def test_product_lift_is_exact_for_the_growing_zeta_shift_family() -> None:
    """Regroup m*s-(m'*r)=delta as one product-coefficient correlation."""
    m_coefficients = {2: F(3, 2), 3: F(-2), 4: F(5, 3)}
    s_coefficients = {5: F(-1), 6: F(2), 7: F(4, 5)}
    left = product_lift_coefficients(m_coefficients, s_coefficients)
    right = product_lift_coefficients(m_coefficients, s_coefficients)

    direct = F(0)
    for m1, m1_weight in m_coefficients.items():
        for s, s_weight in s_coefficients.items():
            for m2, m2_weight in m_coefficients.items():
                for r, r_weight in s_coefficients.items():
                    delta = m1 * s - m2 * r
                    if 0 < abs(delta) <= 5:
                        direct += m1_weight * s_weight * m2_weight * r_weight

    lifted = sum(
        product_lift_shifted_correlation(left, right, delta)
        for delta in range(-5, 6)
        if delta != 0
    )
    assert lifted == direct


def test_q_restricted_full_divisor_sum_is_a_sparse_von_mangoldt_signature() -> None:
    """The completed endpoint divisor sum sees only the q-free part."""
    for q in range(1, 25):
        for n in range(1, 180):
            free = q_free_part(n, q)
            signature = q_restricted_mobius_log_signature(n, q)
            assert signature.mobius_mass == (1 if free == 1 else 0)

            prime_power_base = None
            for prime in type_identity._distinct_prime_factors(free):
                remainder = free
                while remainder % prime == 0:
                    remainder //= prime
                if remainder == 1:
                    prime_power_base = prime
                    break
            expected = (
                () if prime_power_base is None else ((prime_power_base, 1),)
            )
            assert signature.negative_log_prime_coefficients == expected


def test_truncated_selberg_divisor_sum_reflects_only_through_small_cofactors() -> None:
    """Catch dropping the d>N complement when pairing zeta with the mollifier."""
    prime_log_weights = {2: F(2), 3: F(5), 5: F(7), 7: F(11)}
    for cutoff in range(2, 18):
        for n in range(1, 120):
            direct, completed, reflected = truncated_selberg_divisor_sides(
                n,
                cutoff=cutoff,
                normalization=F(13),
                prime_log_weights=prime_log_weights,
            )
            assert direct == completed
            assert direct == reflected

            if n <= cutoff:
                expected = F(1) if n == 1 else F(0)
                for prime in type_identity._distinct_prime_factors(n):
                    remainder = n
                    while remainder % prime == 0:
                        remainder //= prime
                    if remainder == 1:
                        expected = prime_log_weights.get(prime, F(prime)) / 13
                        break
                assert direct == expected


def test_balanced_squarefree_product_has_only_a_strictly_descending_tail() -> None:
    """Catch retaining Lambda(dm) or allowing the reflected endpoint k=m."""
    prime_log_weights = {2: F(2), 3: F(5), 5: F(7), 7: F(11)}
    fixture = type_identity.balanced_selberg_reflection_sides(
        divisor=6,
        cofactor=5,
        cutoff=10,
        normalization=F(13),
        prime_log_weights=prime_log_weights,
    )
    assert fixture.direct == F(-2, 13)
    assert fixture.completed_prime_part == F(0)
    assert fixture.negative_reflected_tail == F(-2, 13)
    assert fixture.reflected_cofactors == (1, 2)

    for cutoff in range(3, 24):
        for divisor in range(2, cutoff + 1):
            if mobius(divisor) == 0:
                continue
            for cofactor in range(2, divisor):
                sides = type_identity.balanced_selberg_reflection_sides(
                    divisor=divisor,
                    cofactor=cofactor,
                    cutoff=cutoff,
                    normalization=F(29),
                    prime_log_weights=prime_log_weights,
                )
                expected_cofactors = tuple(
                    k
                    for k in type_identity.divisors(divisor * cofactor)
                    if k * cutoff < divisor * cofactor
                )
                assert sides.direct == sides.negative_reflected_tail
                assert sides.completed_prime_part == F(0)
                assert sides.reflected_cofactors == expected_cofactors
                assert all(k < cofactor for k in sides.reflected_cofactors)


def test_reflected_pair_energy_keeps_both_nonsymmetric_cross_terms() -> None:
    """Catch merging or discarding either completed-boundary cross term."""
    energy = type_identity.reflected_pair_kernel_energy_sides(
        completed_coefficients={1: F(2), 2: F(3)},
        reflected_coefficients={1: F(5), 2: F(7)},
        pair_kernel={
            (1, 1): F(11),
            (1, 2): F(13),
            (2, 1): F(17),
            (2, 2): F(19),
        },
    )
    assert energy.direct_truncated == F(763)
    assert energy.completed_completed == F(395)
    assert energy.completed_reflected == F(946)
    assert energy.reflected_completed == F(942)
    assert energy.reflected_reflected == F(2256)
    assert energy.expanded == F(763)


def test_reflected_boundary_diagonal_is_an_exact_lcm_sum() -> None:
    """Catch losing floors or the high-gcd/short-quotient restrictions."""
    sides = type_identity.reflected_boundary_diagonal_sides(
        long_weights={6: F(2), 10: F(3), 15: F(5)},
        cutoff=5,
        product_cutoff=60,
    )
    assert sides.direct == F(318)
    assert sides.lcm_sum == F(318)
    assert sides.gcd_parameterized_sum == F(318)
    assert (2, 3, 5) in sides.active_gcd_coordinates
    assert (3, 2, 5) in sides.active_gcd_coordinates
    assert (5, 2, 3) in sides.active_gcd_coordinates
    for common, left, right in sides.active_gcd_coordinates:
        assert F(common) > F(5 * 5, 60)
        assert F(left) < F(60, 5)
        assert F(right) < F(60, 5)


def test_reflected_boundary_pair_kernel_unfolds_to_short_cofactors() -> None:
    """Catch truncating either moving cofactor range in the pair energy."""
    sides = type_identity.reflected_boundary_pair_kernel_sides(
        long_weights={6: F(2), 10: F(3)},
        cutoff=5,
        product_cutoff=30,
        pair_kernel={
            (6, 10): F(5),
            (10, 6): F(7),
            (12, 20): F(11),
            (20, 12): F(13),
            (30, 30): F(17),
        },
    )
    assert sides.direct == F(641)
    assert sides.unfolded == F(641)
    assert (6, 5, 10, 3) in sides.active_factor_pairs
    assert (10, 3, 6, 5) in sides.active_factor_pairs
    for left_divisor, left_cofactor, right_divisor, right_cofactor in (
        sides.active_factor_pairs
    ):
        assert left_divisor * left_cofactor <= 30
        assert right_divisor * right_cofactor <= 30
        assert F(left_cofactor) < F(30, 5)
        assert F(right_cofactor) < F(30, 5)


def test_zero_frequency_master_keeps_both_afe_directions_and_centers_once() -> None:
    """Catch losing a cross term, diagonal, or outer-scale row/column mode."""
    sides = type_identity.zero_frequency_reflected_master_sides(
        completed_coefficients={1: F(1), 2: F(2), 3: F(-1), 4: F(3), 6: F(1)},
        long_left_weights={4: F(2), 5: F(-1)},
        long_right_weights={4: F(2), 5: F(-1)},
        product_cutoff=6,
        secondary_zero_packets=(
            type_identity.SecondaryZeroPacket(
                afe_direction="main",
                poisson_frequency_h=1,
                additive_shift_delta=2,
                dyadic_label="H1-D2",
                pair_kernel={
                    (4, 5): F(2),
                    (5, 4): F(3),
                    (4, 4): F(5),
                    (6, 5): F(7),
                },
            ),
            type_identity.SecondaryZeroPacket(
                afe_direction="dual",
                poisson_frequency_h=-2,
                additive_shift_delta=-3,
                dyadic_label="H2-D3",
                pair_kernel={
                    (4, 5): F(-1),
                    (5, 4): F(4),
                    (5, 5): F(2),
                    (6, 4): F(-2),
                },
            ),
        ),
        explicit_diagonal_weights={4: F(11), 5: F(13), 6: F(17)},
        left_density_weights={4: F(1, 2), 5: F(1, 2)},
        right_density_weights={4: F(1, 2), 5: F(1, 2)},
    )

    assert sides.packet_contributions == (
        ("main", 1, 2, "H1-D2", F(17)),
        ("dual", -2, -3, "H2-D3", F(3)),
    )
    assert sides.afe_direction_contributions == (
        ("main", F(17)),
        ("dual", F(3)),
    )
    assert sides.direct_full_remainder == F(-21)
    assert sides.completed_completed == F(39)
    assert sides.completed_reflected == F(16)
    assert sides.reflected_completed == F(9)
    assert sides.reflected_reflected == F(6)
    assert sides.explicit_diagonal == F(41)
    assert sides.reflected_unfolded == F(6)
    assert (
        sides.resonant_row_component
        + sides.resonant_column_component
        + sides.resonant_grand_component
        == sides.resonant_reflected_projection
    )
    assert sides.resonant_reflected_projection == F(33, 4)
    assert sides.resonant_master_term == F(-75, 4)
    assert sides.centered_remainder == F(-9, 4)
    assert sides.recombined_master_remainder == F(-21)
    assert all(value == 0 for _, value in sides.weighted_centered_row_sums)
    assert all(value == 0 for _, value in sides.weighted_centered_column_sums)


def test_bblr_zero_frequency_reindexes_into_two_outer_coefficients() -> None:
    """Catch losing a factorization or inserting a phase into BBLR's l=0 term."""
    helper = getattr(
        type_identity,
        "bblr_zero_frequency_reindex_sides",
        None,
    )
    assert helper is not None, "BBLR zero-frequency reindex is missing"

    sides = helper(
        left_outer_weights={1: F(2), 2: F(-1)},
        left_inner_weights={3: F(4), 6: F(1)},
        right_outer_weights={1: F(3)},
        right_inner_weights={2: F(5)},
        shift_weights={(2, 1): F(11), (2, 2): F(-1)},
        zero_kernels={(2, 3, 1): F(7)},
    )

    assert sides.direct_sum == F(-2100)
    assert sides.reindexed_sum == F(-2100)
    assert sides.product_pair_sum == F(-2100)
    assert (2, 3, F(-2)) in sides.left_aggregate_entries
    assert (2, 1, F(15)) in sides.right_aggregate_entries
    assert sides.active_coprime_coordinates == ((2, 3, 1),)
    assert sides.labelled_product_pair_kernel_entries == (
        (1, 6, 2, F(77)),
        (2, 6, 2, F(-7)),
    )
    assert sides.combined_product_pair_kernel_entries == ((6, 2, F(70)),)
    assert sides.primitive_to_product_coordinates_are_bijective
    assert sides.original_shift_labels_preserved
    assert sides.secondary_zero_packet_shaped_kernels_constructed
    assert sides.left_and_right_outer_weights_remain_separate
    assert sides.zero_frequency_is_phase_free
    assert not sides.pre_cauchy_stage_identification_proved
    assert not sides.completed_coefficient_identification_proved
    assert not sides.packet_family_exhaustive
    assert not sides.registered_zero_master_identification_proved


def test_bblr_nonzero_frequency_recombines_sectors_before_absolute_values() -> None:
    """Catch separating Type sectors or replacing the original h*delta label."""
    helper = getattr(
        type_identity,
        "bblr_nonzero_frequency_reindex_sides",
        None,
    )
    assert helper is not None, "BBLR nonzero-frequency reindex is missing"

    sides = helper(
        left_outer_weights={1: F(2), 2: F(-1)},
        left_inner_weights={3: F(4), 6: F(1)},
        right_outer_weights={1: F(3)},
        right_inner_weights={2: F(5)},
        labelled_kernels={
            (2, 3, 1, 2, 3, 1): F(7),
            (2, 3, 1, -1, 5, -2): F(11),
        },
    )

    assert sides.direct_sum == F(-540)
    assert sides.reindexed_sum == F(-540)
    assert sides.active_labels == (
        (2, 3, 1, -1, 5, -2, -5, 2),
        (2, 3, 1, 2, 3, 1, 6, 2),
    )
    assert sides.nonzero_poisson_frequencies_retained
    assert sides.original_shift_and_delta_labels_retained
    assert sides.product_frequency_h_times_delta_preserved
    assert sides.poisson_product_h_times_l_preserved
    assert sides.type_factorizations_recombined_before_absolute_values
    assert sides.left_and_right_mobius_families_remain_separate
    assert not sides.global_ttstar_estimate_proved


def test_bblr_ttstar_resonance_is_exact_reciprocal_phase_collision() -> None:
    helper = getattr(
        type_identity,
        "bblr_reciprocal_phase_collision_audit",
        None,
    )
    assert helper is not None, "BBLR reciprocal-phase collision audit is missing"

    collision = helper(
        left_x=2,
        left_y=5,
        left_h=1,
        left_delta=7,
        left_l=1,
        right_x=3,
        right_y=5,
        right_h=2,
        right_delta=11,
        right_l=2,
    )
    assert collision.left_phase_mod_one == F(2, 5)
    assert collision.right_phase_mod_one == F(2, 5)
    assert collision.common_phase_modulus == 5
    assert collision.cross_phase_numerator == 0
    assert collision.exact_phase_collision
    assert not collision.identical_rows
    assert collision.left_original_product_frequency == 7
    assert collision.right_original_product_frequency == 22
    assert collision.left_poisson_product == 1
    assert collision.right_poisson_product == 4
    assert collision.resonance_can_join_distinct_product_frequencies


def test_bblr_ttstar_keeps_signed_cross_terms_inside_each_phase_class() -> None:
    helper = getattr(
        type_identity,
        "bblr_phase_group_ttstar_sides",
        None,
    )
    assert helper is not None, "BBLR phase-group TT* identity is missing"

    sides = helper(
        rows=(
            ("u", 2, 5, 1, 7, 1, F(2)),
            ("v", 3, 5, 2, 11, 2, F(-1)),
            ("w", 1, 5, 1, 13, 1, F(3)),
        )
    )
    assert sides.common_phase_modulus == 5
    assert sides.phase_groups == (
        (F(2, 5), ("u", "v")),
        (F(4, 5), ("w",)),
    )
    assert sides.identity_diagonal_quadratic == F(70)
    assert sides.distinct_collision_quadratic == F(-20)
    assert sides.orthogonality_quadratic == F(50)
    assert sides.signed_cross_terms_can_cancel_identity_diagonal
    assert not sides.product_frequency_partition_diagonalizes_ttstar
    assert not sides.absolute_value_phase_classes_reach_target_proved


def test_bblr_near_diagonal_rows_form_a_large_slow_phase_packet() -> None:
    helper = getattr(
        type_identity,
        "bblr_near_diagonal_resonance_certificate",
        None,
    )
    assert helper is not None, "BBLR near-diagonal resonance helper is missing"

    certificate = helper(
        modulus_y=1009,
        gap_c=10,
        residue_min=9,
        residue_max=11,
        frequency_min=80,
        frequency_max=100,
        phase_center_residue=10,
    )

    assert certificate.reciprocal_x == 1019
    assert certificate.inverse_x_mod_y == 101
    assert certificate.resonant_h_values == (90, 100, 110)
    assert certificate.phase_residues == (9, 10, 11)
    assert certificate.all_near_diagonal_congruences_verified
    assert certificate.max_absolute_centered_phase_turns == F(100, 1009)
    assert certificate.packet_lies_in_positive_real_half_plane
    assert certificate.term_count == 63
    assert certificate.absolute_majorant_real_part_lower_bound == F(63, 2)
    assert not certificate.local_h_l_completion_alone_reaches_gate


def test_bblr_inverse_phase_has_exact_gap_determinant_coordinates() -> None:
    helper = getattr(
        type_identity,
        "bblr_gap_resonance_coordinates",
        None,
    )
    assert helper is not None, "BBLR gap-resonance coordinates are missing"

    principal = helper(x=1019, y=1009, h=100)
    assert principal.gap_c == 10
    assert principal.inverse_x_mod_y == 101
    assert principal.phase_residue_r == 10
    assert principal.determinant_index_k == 0
    assert principal.gap_determinant_identity_verified
    assert principal.principal_near_diagonal_incidence

    nonprincipal = helper(x=111, y=101, h=91)
    assert nonprincipal.gap_c == 10
    assert nonprincipal.inverse_x_mod_y == 91
    assert nonprincipal.phase_residue_r == 100
    assert nonprincipal.determinant_index_k == 9
    assert nonprincipal.gap_determinant_identity_verified
    assert not nonprincipal.principal_near_diagonal_incidence


def test_bblr_principal_gap_is_a_partial_diagonal_solution_line() -> None:
    helper = getattr(
        type_identity,
        "bblr_principal_incidence_solution_line",
        None,
    )
    assert helper is not None, "BBLR principal solution-line helper is missing"

    diagonal = helper(x=11, y=7, r=5, m2=5, n2=5)
    assert diagonal.shift_h == 20
    assert diagonal.line_parameter_t == 0
    assert diagonal.solution_line_identity_verified
    assert diagonal.short_inner_support_forces_t_zero
    assert diagonal.partial_diagonal_m2_equals_n2_equals_r

    translated = helper(x=11, y=7, r=5, m2=19, n2=27)
    assert translated.shift_h == 20
    assert translated.line_parameter_t == 2
    assert translated.solution_line_identity_verified
    assert not translated.short_inner_support_forces_t_zero
    assert not translated.partial_diagonal_m2_equals_n2_equals_r


def test_bblr_partial_diagonal_reindexes_as_additive_band_correlation() -> None:
    helper = getattr(
        type_identity,
        "bblr_partial_diagonal_correlation_sides",
        None,
    )
    assert helper is not None, "BBLR partial-diagonal correlation is missing"

    sides = helper(
        left_outer_weights={1: F(2), 2: F(-1)},
        left_inner_weights={3: F(4)},
        right_outer_weights={1: F(3)},
        right_inner_weights={2: F(5), 3: F(1), 9: F(2)},
        left_second_weights={1: F(2), 2: F(1)},
        right_second_weights={1: F(3), 2: F(-1)},
        shift_weights={h: F(1) for h in (1, 2, 3, 4, 6, 8, 12)},
    )

    assert sides.direct_plus_sum == F(240)
    assert sides.direct_minus_sum == F(120)
    assert sides.direct_combined_sum == F(360)
    assert sides.product_pair_correlation_sum == F(360)
    assert sides.factorized_to_product_pair_identity_verified
    assert sides.plus_minus_exhaust_every_unequal_product_pair
    assert sides.common_second_factor_retained
    assert sides.equal_product_diagonal_excluded
    assert not sides.analytic_afe_packet_exhaustive
    assert not sides.original_zeta_mollifier_coefficient_adapter_proved
    assert not sides.partial_diagonal_target_bound_proved


def test_additive_band_extracts_its_constant_fourier_mode_exactly() -> None:
    helper = getattr(
        type_identity,
        "additive_band_zero_mode_sides",
        None,
    )
    assert helper is not None, "additive-band zero-mode helper is missing"

    sides = helper(
        modulus=5,
        left_coefficients={0: F(2), 1: F(-1), 3: F(4)},
        right_coefficients={0: F(3), 2: F(5)},
        labelled_shift_kernels={
            "main/order-1": {1: F(2), 2: F(-1)},
            "dual/order-2": {1: F(-1), 3: F(4)},
        },
    )

    assert sides.direct_band_sum == F(105)
    assert sides.combined_kernel_mean == F(4, 5)
    assert sides.constant_mode_contribution == F(32)
    assert sides.centered_band_sum == F(73)
    assert sides.recombined_band_sum == F(105)
    assert sides.centered_kernel_shift_sum == F(0)
    assert sides.zero_mode_extraction_identity_verified
    assert sides.packet_labels_retained == (
        "dual/order-2",
        "main/order-1",
    )
    assert not sides.combined_packet_zero_mode_vanishes
    assert not sides.analytic_afe_ordering_kernel_derived


def test_bblr_master_partitions_exactly_by_outer_product_gap() -> None:
    helper = getattr(
        type_identity,
        "bblr_near_diagonal_outer_correlation_sides",
        None,
    )
    assert helper is not None, "BBLR near-diagonal outer adapter is missing"

    sides = helper(
        left_outer_weights={1: F(2), 2: F(-1)},
        left_inner_weights={3: F(4), 6: F(1)},
        right_outer_weights={1: F(3)},
        right_inner_weights={2: F(5), 3: F(1), 5: F(-1)},
        labelled_kernels={
            (1, 3, 2, 2, 3, 1): F(7),
            (2, 3, 1, 2, 3, 1): F(11),
            (1, 3, 5, 2, 3, 1): F(13),
            (3, 1, 1, 2, 3, 1): F(17),
        },
        positive_gap_min=1,
        positive_gap_max=2,
    )

    assert sides.direct_sum == F(606)
    assert sides.reindexed_sum == F(606)
    assert sides.positive_near_diagonal_sum == F(510)
    assert sides.positive_principal_incidence_sum == F(0)
    assert sides.positive_nonprincipal_incidence_sum == F(510)
    assert sides.zero_gap_sum == F(408)
    assert sides.negative_or_far_gap_sum == F(-312)
    assert sides.positive_near_diagonal_entries == (
        (1, 1, 2, 3, 2, 3, 1, F(840)),
        (2, 2, 1, 3, 2, 3, 1, F(-330)),
    )
    assert sides.full_gap_partition_identity_verified
    assert sides.principal_incidence_partition_verified
    assert sides.type_factorizations_recombined_before_gap_partition
    assert sides.all_h_delta_l_labels_preserved
    assert not sides.original_coupled_kernel_stage_exhaustive


def test_zero_frequency_master_rejects_the_already_counted_original_zero_mode() -> None:
    """The h=0 term belongs to (4.6), not the secondary completion master."""
    with pytest.raises(ValueError, match="original h=0"):
        type_identity.zero_frequency_reflected_master_sides(
            completed_coefficients={1: F(1)},
            long_left_weights={1: F(1)},
            long_right_weights={1: F(1)},
            product_cutoff=1,
            secondary_zero_packets=(
                type_identity.SecondaryZeroPacket(
                    afe_direction="main",
                    poisson_frequency_h=0,
                    additive_shift_delta=1,
                    dyadic_label="zero",
                    pair_kernel={(1, 1): F(1)},
                ),
            ),
            explicit_diagonal_weights={1: F(1)},
            left_density_weights={1: F(1)},
            right_density_weights={1: F(1)},
        )


def test_zero_frequency_centering_is_not_canonical_until_density_is_derived() -> None:
    """Changing p,q moves mass between M_res and R_cent, not their sum."""
    packets = (
        type_identity.SecondaryZeroPacket(
            "main", 1, 2, "H1-D2", {(4, 4): F(5), (4, 5): F(2)}
        ),
        type_identity.SecondaryZeroPacket(
            "dual", -2, 3, "H2-D3", {(5, 4): F(4), (5, 5): F(2)}
        ),
    )
    common = {
        "completed_coefficients": {4: F(3), 5: F(-1)},
        "long_left_weights": {4: F(2), 5: F(-1)},
        "long_right_weights": {4: F(2), 5: F(-1)},
        "product_cutoff": 5,
        "secondary_zero_packets": packets,
        "explicit_diagonal_weights": {4: F(11), 5: F(13)},
    }
    uniform = type_identity.zero_frequency_reflected_master_sides(
        **common,
        left_density_weights={4: F(1, 2), 5: F(1, 2)},
        right_density_weights={4: F(1, 2), 5: F(1, 2)},
    )
    endpoint = type_identity.zero_frequency_reflected_master_sides(
        **common,
        left_density_weights={4: F(1), 5: F(0)},
        right_density_weights={4: F(0), 5: F(1)},
    )

    assert (
        uniform.recombined_master_remainder
        == endpoint.recombined_master_remainder
    )
    assert uniform.resonant_master_term != endpoint.resonant_master_term
    assert uniform.centered_remainder != endpoint.centered_remainder


def test_zero_frequency_master_requires_probability_density_weights() -> None:
    packet = type_identity.SecondaryZeroPacket(
        "main", 1, 1, "unit", {(1, 1): F(1)}
    )
    with pytest.raises(ValueError, match="nonnegative"):
        type_identity.zero_frequency_reflected_master_sides(
            completed_coefficients={1: F(1)},
            long_left_weights={1: F(1), 2: F(1)},
            long_right_weights={1: F(1)},
            product_cutoff=2,
            secondary_zero_packets=(packet,),
            explicit_diagonal_weights={1: F(1)},
            left_density_weights={1: F(2), 2: F(-1)},
            right_density_weights={1: F(1)},
        )


def test_centered_operator_gate_records_the_exact_t_squared_saving() -> None:
    """Raw T^5 to target T^3 means T^2, or T^4 after TT*."""
    ledger = type_identity.centered_operator_saving_ledger(
        raw_sum_exponent=F(5),
        target_sum_exponent=F(3),
    )

    assert ledger.required_operator_saving_exponent == F(2)
    assert ledger.required_ttstar_saving_exponent == F(4)
    assert ledger.fixed_coefficient_operator_gate_is_sufficient
    assert ledger.uniform_unit_ball_operator_gate_is_equivalent


def test_coupled_ttstar_splits_parallel_and_nonparallel_slopes_exactly() -> None:
    """The determinant-zero orbit is separated before any spectral bound."""
    split = type_identity.coupled_ttstar_determinant_split_sides(
        rows=(
            type_identity.CoupledOperatorRow("u", 1, 1),
            type_identity.CoupledOperatorRow("v", 1, 1),
            type_identity.CoupledOperatorRow("w", 1, 2),
        ),
        columns=("t0", "t1"),
        operator_entries={
            ("u", "t0"): F(1),
            ("u", "t1"): F(2),
            ("v", "t0"): F(-1),
            ("v", "t1"): F(3),
            ("w", "t0"): F(4),
            ("w", "t1"): F(-2),
        },
        row_coefficients={"u": F(2), "v": F(-1), "w": F(3)},
    )

    assert split.direct_quadratic == split.gram_quadratic
    assert (
        split.determinant_zero_quadratic
        + split.determinant_nonzero_quadratic
        == split.gram_quadratic
    )
    assert split.determinant_zero_pairs == (
        ("u", "u"),
        ("u", "v"),
        ("v", "u"),
        ("v", "v"),
        ("w", "w"),
    )


def test_coupled_ttstar_rejects_nonprimitive_affine_slopes() -> None:
    with pytest.raises(ValueError, match="positive primitive"):
        type_identity.coupled_ttstar_determinant_split_sides(
            rows=(type_identity.CoupledOperatorRow("bad", 2, 2),),
            columns=("t",),
            operator_entries={("bad", "t"): F(1)},
            row_coefficients={"bad": F(1)},
        )


def test_zeta_variables_pair_exactly_with_their_mollifier_divisors() -> None:
    """Catch retaining four variables after the exact x=nd, y=me regrouping."""
    direct, paired = zeta_mollifier_pairing_sides(
        mollifier_weights=((1, F(2)), (2, F(-1))),
        zeta_indices=(1, 3),
        completely_multiplicative_weight=lambda value: F(value * value),
        shift_weights={
            -5: F(7),
            -4: F(11),
            -2: F(13),
            -1: F(17),
            0: F(19),
            1: F(23),
            2: F(29),
            4: F(31),
            5: F(37),
        },
    )
    assert direct == F(8088)
    assert paired == F(8088)


def test_common_mellin_mode_recombines_only_the_zeta_index_product() -> None:
    """Catch treating the one Mellin mode as two independent averages."""
    direct, paired = type_identity.common_mellin_product_constraint_sides(
        mollifier_weights=((1, F(2)), (2, F(-1))),
        zeta_weights=((1, F(3)), (3, F(5))),
        completely_multiplicative_weight=F,
        mellin_mode_weights=((0, F(7)), (1, F(11)), (-1, F(13))),
    )
    assert direct == F(44_096, 9)
    assert paired == F(44_096, 9)


def test_common_mellin_recombination_retains_the_product_pair_kernel() -> None:
    """Catch dropping the shifted x,y kernel during Mellin recombination."""
    pair_weights = {
        (1, 1): F(5),
        (1, 2): F(7),
        (2, 1): F(11),
        (2, 2): F(13),
    }
    direct, paired = type_identity.common_mellin_product_constraint_sides(
        mollifier_weights=((1, F(1)),),
        zeta_weights=((1, F(2)), (2, F(3))),
        completely_multiplicative_weight=F,
        mellin_mode_weights=((0, F(1)), (1, F(2))),
        product_pair_weights=pair_weights,
    )
    assert direct == F(903, 2)
    assert paired == F(903, 2)


def test_centering_moves_the_complete_pole_mass_to_the_product_boundary() -> None:
    mollifier_weights = (
        (1, F(2)),
        (2, F(-3, 2)),
        (3, F(5, 3)),
        (6, F(-7, 5)),
        (2, F(1, 2)),
    )
    for product_cutoff in range(1, 18):
        direct, recombined, _ = centered_selberg_product_boundary_sides(
            mollifier_weights=mollifier_weights,
            product_cutoff=product_cutoff,
            completely_multiplicative_weight=lambda value: F(value * value),
            density=F(11, 7),
        )
        assert direct == recombined

        combined = {1: F(2), 2: F(-1), 3: F(5, 3), 6: F(-7, 5)}
        pole_density = sum(
            (
                weight / divisor
                for divisor, weight in combined.items()
            ),
            F(0),
        )
        pole_direct, pole_recombined, boundary = (
            centered_selberg_product_boundary_sides(
                mollifier_weights=mollifier_weights,
                product_cutoff=product_cutoff,
                completely_multiplicative_weight=lambda value: F(1, value),
                density=pole_density,
            )
        )
        assert pole_direct == pole_recombined
        assert pole_direct == -boundary


def test_q_restricted_twisted_divisor_sum_has_exact_euler_derivative() -> None:
    """Verify log(X) P(z)-P'(z) in independent formal prime twists."""
    for q in range(1, 12):
        for n in range(1, 90):
            free_primes = type_identity._distinct_prime_factors(
                q_free_part(n, q)
            )
            twists = {prime: F(prime, prime + 1) for prime in free_primes}
            signature = q_restricted_twisted_log_signature(n, q, twists)
            expected_mass = F(1)
            for prime in free_primes:
                expected_mass *= 1 - twists[prime]
            assert signature.twisted_mobius_mass == expected_mass

            expected_logs = []
            for prime in free_primes:
                coefficient = twists[prime]
                for other in free_primes:
                    if other != prime:
                        coefficient *= 1 - twists[other]
                expected_logs.append((prime, coefficient))
            assert signature.negative_log_prime_coefficients == tuple(
                expected_logs
            )


def test_coprime_product_lift_equals_one_common_divisor_sum() -> None:
    """Verify the exact c-sum used by the zero-line transition energy."""
    for q in range(1, 8):
        for n_left in range(1, 24):
            for n_right in range(1, 24):
                cutoff = 11
                identity = coprime_divisor_pair_identity(
                    n_left,
                    n_right,
                    q=q,
                    cutoff=cutoff,
                    left_weight=lambda d: F(d + 1, d + 2),
                    right_weight=lambda d: F(2 * d + 1, d + 3),
                )
                assert identity.direct_coprime_sum == identity.mobius_inverted_sum
                for common_divisor in identity.active_common_divisors:
                    assert (n_left - n_right) % common_divisor == 0


def test_squared_type_ii_phase_compresses_to_the_lcm_modulus() -> None:
    """Verify the minimal common-b conductor on exhaustive small fixtures."""
    adapter = getattr(type_identity, "lcm_b_phase_compression", None)
    assert adapter is not None, "lcm b-phase helper is missing"

    for s1 in range(2, 10):
        for s2 in range(2, 10):
            for a1 in range(1, 8):
                for a2 in range(1, 8):
                    for b in range(1, 8):
                        if gcd(a1 * b, s1) != 1:
                            continue
                        if gcd(a2 * b, s2) != 1:
                            continue
                        for n1 in (-5, -1, 1, 4):
                            for n2 in (-3, 2, 6):
                                audit = adapter(
                                    n1=n1,
                                    a1=a1,
                                    s1=s1,
                                    n2=n2,
                                    a2=a2,
                                    s2=s2,
                                    b=b,
                                )
                                assert audit.lcm_modulus == (
                                    s1 * s2 // gcd(s1, s2)
                                )
                                assert audit.original_phase == (
                                    audit.compressed_phase
                                )


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


def test_double_zero_sums_leave_theta_00_as_the_nonzero_mass() -> None:
    adapter = getattr(
        type_identity,
        "double_zero_sum_nonzero_mass",
        None,
    )
    assert adapter is not None, "double-zero-sum mass helper is missing"

    theta = (
        (F(7), F(-2), F(-5)),
        (F(-3), F(11), F(-8)),
        (F(-4), F(-9), F(13)),
    )
    nonzero_mass, theta_00 = adapter(theta)
    assert nonzero_mass == theta_00 == F(7)
    with pytest.raises(ValueError, match="row and column sums"):
        adapter(((F(1), F(0)), (F(0), F(0))))


def test_squarefree_coprimality_expansion_is_exact_before_e_poisson() -> None:
    adapter = getattr(
        type_identity,
        "restricted_squarefree_expansion",
        None,
    )
    assert adapter is not None, "restricted squarefree expansion is missing"

    for e in range(1, 80):
        for modulus in range(1, 30):
            expected = int(mobius(e) != 0 and gcd(e, modulus) == 1)
            assert adapter(e=e, modulus=modulus) == expected


def test_long_cutoff_quotient_congruence_reduces_by_the_exact_gcd() -> None:
    adapter = getattr(
        type_identity,
        "long_cutoff_quotient_progression",
        None,
    )
    assert adapter is not None, "long-cutoff quotient progression is missing"

    # 3*s + 5 is divisible by 14 exactly when s == 3 (mod 14).
    assert adapter(j=3, delta=5, b=2, d=1, v=7) == (14, 3)

    # gcd(6, 14)=2 and 2|8, so the reduced modulus is 7.
    modulus, residue = adapter(j=6, delta=8, b=2, d=1, v=7)
    assert (modulus, residue) == (7, 1)
    for s in range(-20, 21):
        assert ((6 * s + 8) % 14 == 0) == (s % modulus == residue)

    # gcd(6, 14)=2 does not divide 5, hence there is no quotient integer.
    assert adapter(j=6, delta=5, b=2, d=1, v=7) is None


def test_long_cutoff_quotient_progression_rejects_zero_or_negative_factors() -> None:
    adapter = getattr(
        type_identity,
        "long_cutoff_quotient_progression",
        None,
    )
    assert adapter is not None, "long-cutoff quotient progression is missing"
    with pytest.raises(ValueError, match="b,d must be positive and v nonzero"):
        adapter(j=1, delta=1, b=0, d=1, v=1)


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
        r"\mathfrak Z_q(B,V;\mathcal D)",
        r"e\!\left(\frac{bdecv}{s}\right)-1",
        r"\mathrm{QCT}_{B,V,\mathcal D}",
        r"\frac{1751}{1000}",
        r"\frac{751}{1000}",
        r"\mu^2(e)\mathbf1_{(e,M)=1}",
        r"\widehat W_{c,v}\!\left(\frac{m}{g}-\alpha\right)",
        r"\sum_{\substack{c\ne0\\v\ne0}}\Theta_{r,s}(c,v)",
        r"=\Theta_{r,s}(0,0)",
        r"bdev-h=js",
        "centered e-Poisson status: no new conductor",
        "new spectral proposition status: unproved",
    ):
        assert marker in text
    assert "unconditional asymptotic proved" not in text
