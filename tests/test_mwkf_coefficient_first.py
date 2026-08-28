import sys
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.mwkf_coefficient_first import (
    coefficient_first_scales,
    coefficient_region,
    formal_log,
    formal_von_mangoldt,
    missing_convolution_divisors,
    scaled_boundary_correction,
    restricted_complementary_divisor_partition,
    scaled_truncated_product_coefficient,
    scaled_zeta_mollifier_coefficient,
    zero_route_audit,
)


def test_formal_log_and_von_mangoldt_are_exact_prime_vectors() -> None:
    assert formal_log(12) == {2: 2, 3: 1}
    assert formal_von_mangoldt(8) == {2: 1}
    assert formal_von_mangoldt(25) == {5: 1}
    assert formal_von_mangoldt(12) == {}


def test_complete_convolution_is_lambda_before_the_mollifier_boundary() -> None:
    cutoff_n = 30
    assert scaled_zeta_mollifier_coefficient(1, cutoff_n) == {
        2: 1,
        3: 1,
        5: 1,
    }
    assert scaled_zeta_mollifier_coefficient(8, cutoff_n) == {2: 1}
    assert scaled_zeta_mollifier_coefficient(12, cutoff_n) == {}
    assert scaled_zeta_mollifier_coefficient(25, cutoff_n) == {5: 1}
    assert coefficient_region(25, cutoff_n) == "von_mangoldt"


def test_infinite_zeta_boundary_has_the_exact_tail_sign() -> None:
    # For n=14 and N=10 the only omitted divisor with nonzero Mobius
    # coefficient is d=14.  Thus log(N)b_N(14)=log(14/10)=log(7/5).
    assert missing_convolution_divisors(14, cutoff_n=10) == (14,)
    assert scaled_boundary_correction(14, cutoff_n=10) == {5: -1, 7: 1}
    assert scaled_zeta_mollifier_coefficient(14, cutoff_n=10) == {
        5: -1,
        7: 1,
    }
    assert coefficient_region(14, cutoff_n=10) == "boundary"


def test_finite_zeta_cutoff_creates_a_second_exact_boundary() -> None:
    # N=30 contains every divisor of 6, but zeta cutoff X=5 omits the
    # factorization 6=1*6.  The scaled coefficient is therefore -log(30).
    assert missing_convolution_divisors(6, cutoff_n=30, cutoff_x=5) == (1,)
    assert scaled_truncated_product_coefficient(
        6, cutoff_n=30, cutoff_x=5
    ) == {2: -1, 3: -1, 5: -1}
    assert coefficient_region(6, cutoff_n=30, cutoff_x=5) == "boundary"


def test_truncated_product_recovers_lambda_on_its_complete_region() -> None:
    for n in range(2, 31):
        assert scaled_truncated_product_coefficient(
            n, cutoff_n=30, cutoff_x=30
        ) == formal_von_mangoldt(n)


def test_standard_zeta_afe_only_has_a_half_power_complete_region() -> None:
    scales = coefficient_first_scales(
        mollifier_exponent=F(3), zeta_cutoff_exponent=F(1, 2)
    )
    assert scales.complete_lambda_region == F(1, 2)
    assert scales.product_support == F(7, 2)
    assert scales.euler_maclaurin_pole == F(-3, 4)


def test_truncating_zeta_at_the_mollifier_length_has_a_large_pole_term() -> None:
    scales = coefficient_first_scales(
        mollifier_exponent=F(3), zeta_cutoff_exponent=F(3)
    )
    assert scales.complete_lambda_region == F(3)
    assert scales.product_support == F(6)
    # X^(1-s)/(s-1) has size T^(x/2-1) on Re(s)=1/2.
    assert scales.euler_maclaurin_pole == F(1, 2)


def test_perron_zero_residue_amplifies_an_off_line_zero() -> None:
    audit = zero_route_audit(
        mollifier_exponent=F(3),
        zero_real_part=F(3, 4),
        all_lengths_up_to_cutoff=False,
    )
    assert audit.zero_residue_amplification == F(3, 4)
    assert audit.origin_interval_zero_free_boundary == F(2, 3)
    assert audit.dyadic_interval_zero_free_boundary == F(7, 6)


def test_single_mollifier_length_does_not_meet_bettin_gonek_scope() -> None:
    audit = zero_route_audit(
        mollifier_exponent=F(3),
        zero_real_part=F(1, 2),
        all_lengths_up_to_cutoff=False,
    )
    assert audit.zero_residue_amplification == F(0)
    assert not audit.bettin_gonek_applicable
    assert audit.reason == "requires_all_lengths_up_to_T_theta"


def test_critical_complementary_divisor_pair_leaves_two_exact_residuals() -> None:
    # Here n/X=105/11 lies in the complementary-divisor collar [5,10].
    # The available boundary term and the reflected tail below 5 therefore
    # do not complete the restricted divisor convolution by themselves:
    # the boundary-tail terms 5<=m<10 and the available scales m>10 remain.
    audit = restricted_complementary_divisor_partition(
        210,
        cutoff_x=22,
        modulus_q=1,
        boundary_p=5,
    )
    assert audit.critical_collar
    assert audit.boundary_available
    assert audit.below_boundary_tail
    assert audit.boundary_tail
    assert audit.above_boundary_available
    assert audit.complete == {}
    assert audit.paired_boundary_plus_lower_tail
    assert audit.unpaired_boundary_plus_upper
    assert audit.paired_boundary_plus_lower_tail == {
        prime: -exponent
        for prime, exponent in audit.unpaired_boundary_plus_upper.items()
    }
    assert audit.complete_identity_holds
    assert audit.complete_matches_sparse_formula
    assert not audit.pair_closes_completion


def test_available_upper_scale_can_cross_the_two_sided_afe_transition() -> None:
    # The same n has a boundary representation 102=3*34 and an upper
    # representation 102=6*17.  Both reduced divisors are squarefree,
    # coprime to q=5, and below X=35.  Repeating the upper representation
    # on both sides gives 6^2>35, so completing the boundary box can move
    # a polylog-sized zeta pair across the model AFE product transition.
    audit = restricted_complementary_divisor_partition(
        102,
        cutoff_x=35,
        modulus_q=5,
        boundary_p=2,
    )
    assert 34 in audit.boundary_available_divisors
    assert 17 in audit.above_boundary_available_divisors
    assert 102 // 34 == 3
    assert 102 // 17 == 6
    assert (102 // 17) ** 2 > 35
    assert audit.complete_identity_holds
    assert audit.complete_matches_sparse_formula
    assert not audit.pair_closes_completion


def test_restricted_completion_retains_the_q_smooth_mass_term() -> None:
    audit = restricted_complementary_divisor_partition(
        40,
        cutoff_x=10,
        modulus_q=10,
        boundary_p=2,
    )
    assert audit.complete == formal_log(10)
    assert audit.sparse_completion == formal_log(10)
    assert audit.complete_matches_sparse_formula
