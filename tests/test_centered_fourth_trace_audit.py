import sys
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.audit_centered_fourth_trace import (
    admissible_projective_cycle_count,
    discriminant_multiplicities,
    fourth_trace_discriminant,
    fourth_trace_formula,
    fourth_trace_matrix,
    inverse_cycle_solution_count,
    is_proposition_degenerate,
    jacobi_symbol,
    multiplicity_energy,
    projective_fixed_point_count,
    projective_level,
    representation_character_prime,
    scalar_congruence_roots,
)


def test_fourth_trace_formula_matches_matrix_word_exhaustively() -> None:
    assert fourth_trace_formula((1, 1, 1, 1)) == -1
    assert fourth_trace_discriminant((1, 1, 1, 1)) == -3
    assert fourth_trace_formula((1, 2, 3, 4)) == 2
    assert fourth_trace_discriminant((1, 2, 3, 4)) == 0
    for frequencies in product(range(-2, 3), repeat=4):
        assert fourth_trace_matrix(frequencies) == fourth_trace_formula(frequencies)


def test_alternating_multiplier_trace_formula_matches_the_paper_word() -> None:
    frequencies = (1, 2, 3, 4)
    for odd_multiplier in (-3, -1, 1, 2):
        expected = (
            odd_multiplier**2 * 1 * 2 * 3 * 4
            - odd_multiplier * (1 + 3) * (2 + 4)
            + 2
        )
        assert fourth_trace_formula(
            frequencies, odd_multiplier=odd_multiplier
        ) == expected
        assert fourth_trace_matrix(
            frequencies, odd_multiplier=odd_multiplier
        ) == expected

    for frequencies in product(range(-1, 2), repeat=4):
        for odd_multiplier in (-2, -1, 1, 2):
            assert fourth_trace_matrix(
                frequencies, odd_multiplier=odd_multiplier
            ) == fourth_trace_formula(
                frequencies, odd_multiplier=odd_multiplier
            )


def test_published_exceptional_strata_are_kept_explicit() -> None:
    assert is_proposition_degenerate((0, 1, 1, 1))
    assert is_proposition_degenerate((1, 0, 1, 1))
    assert is_proposition_degenerate((1, 1, 0, 1))
    assert is_proposition_degenerate((2, 1, -2, 1))
    assert not is_proposition_degenerate((1, 1, 1, 1))
    assert not is_proposition_degenerate((1, 1, 1, 0))


def test_jacobi_symbol_is_multiplicative_and_has_euler_prime_values() -> None:
    for odd_prime in (3, 5, 7, 11, 13):
        for value in range(-20, 21):
            expected = 0 if value % odd_prime == 0 else (
                1 if pow(value, (odd_prime - 1) // 2, odd_prime) == 1 else -1
            )
            assert jacobi_symbol(value, odd_prime) == expected
    for value in range(-20, 21):
        assert jacobi_symbol(value, 5 * 13) == (
            jacobi_symbol(value, 5) * jacobi_symbol(value, 13)
        )


def test_raw_inverse_cycle_count_is_not_the_representation_character() -> None:
    frequencies = (1, 1, 1, 2)
    prime = 5
    assert inverse_cycle_solution_count(frequencies, prime) == 0
    assert admissible_projective_cycle_count(frequencies, prime) == 0
    assert projective_fixed_point_count(frequencies, prime) == 1
    assert fourth_trace_discriminant(frequencies) == 0
    assert 1 + jacobi_symbol(fourth_trace_discriminant(frequencies), prime) == 1


def test_projective_fixed_points_equal_one_plus_representation_character() -> None:
    for prime in (3, 5):
        for frequencies in product(range(prime), repeat=4):
            assert projective_fixed_point_count(frequencies, prime) == (
                1 + representation_character_prime(frequencies, prime)
            )
            assert inverse_cycle_solution_count(frequencies, prime) == (
                admissible_projective_cycle_count(frequencies, prime)
            )


def test_alternating_multiplier_projective_character_identity() -> None:
    prime = 5
    for odd_multiplier in (1, 2, 3, 4):
        for frequencies in product(range(3), repeat=4):
            assert projective_fixed_point_count(
                frequencies, prime, odd_multiplier=odd_multiplier
            ) == 1 + representation_character_prime(
                frequencies, prime, odd_multiplier=odd_multiplier
            )


def test_scalar_trace_word_uses_the_exceptional_character_value() -> None:
    frequencies = (0, 0, 0, 0)
    for prime in (3, 5, 7):
        assert representation_character_prime(frequencies, prime) == prime
        assert projective_fixed_point_count(frequencies, prime) == prime + 1


def test_level_and_scalar_congruence_strata_match_the_published_condition() -> None:
    assert projective_level((0, 0, 0, 0)) == 0
    assert projective_level((-2, -1, -2, -1)) == 0
    assert projective_level((1, 1, 1, 1)) == 1
    assert projective_level((-4, -4, -4, -4)) == 56

    assert scalar_congruence_roots((0, 0, 0, 0), 15) == (1,)
    assert scalar_congruence_roots((-2, -1, -2, -1), 15) == (14,)
    assert scalar_congruence_roots((1, 1, 1, 1), 15) == ()
    for divisor in (1, 2, 4, 7, 8, 14, 28, 56):
        roots = scalar_congruence_roots((-4, -4, -4, -4), divisor)
        assert bool(roots) == (56 % divisor == 0)


def test_discriminant_multiplicity_energy_has_literal_small_box_values() -> None:
    multiplicities = discriminant_multiplicities(1)
    assert sum(multiplicities.values()) == 16
    assert dict(multiplicities) == {-3: 10, 5: 4, 45: 2}
    assert multiplicity_energy(multiplicities) == 120


def test_excluding_published_degenerates_changes_the_finite_family() -> None:
    multiplicities = discriminant_multiplicities(1, exclude_degenerate=True)
    assert sum(multiplicities.values()) == 8
    assert dict(multiplicities) == {-3: 6, 45: 2}
    assert multiplicity_energy(multiplicities) == 40
