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
    determinant_cokernel_coordinates,
    determinant_line_coordinates,
    determinant_line_coprimality_indicator,
    determinant_line_coprimality_residue,
    determinant_lattice_solution,
    determinant_slope_square_coordinates,
    endpoint_density_convolution_coefficient,
    endpoint_q_density,
    endpoint_weighted_mobius,
    mobius,
    product_lift_coefficients,
    product_lift_shifted_correlation,
    coprime_divisor_pair_identity,
    q_free_part,
    q_restricted_mobius_log_signature,
    q_restricted_twisted_log_signature,
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
