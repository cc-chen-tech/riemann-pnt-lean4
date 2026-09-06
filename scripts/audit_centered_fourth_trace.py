"""Finite audit for the centered fourth-trace route.

This module checks the integral SL(2) trace identity, its quadratic
discriminant, and small finite exceptional/collision families.  It does not
identify the resulting representation character with the Selberg-mollifier
coupled kernel and therefore does not prove the residual Type-II gate.
"""

from __future__ import annotations

from collections import Counter
from collections.abc import Mapping
from itertools import product
from math import gcd, isqrt

Matrix2 = tuple[tuple[int, int], tuple[int, int]]
Frequency4 = tuple[int, int, int, int]


def _matrix_multiply(left: Matrix2, right: Matrix2) -> Matrix2:
    return (
        (
            left[0][0] * right[0][0] + left[0][1] * right[1][0],
            left[0][0] * right[0][1] + left[0][1] * right[1][1],
        ),
        (
            left[1][0] * right[0][0] + left[1][1] * right[1][0],
            left[1][0] * right[0][1] + left[1][1] * right[1][1],
        ),
    )


def _translation(frequency: int) -> Matrix2:
    return ((1, frequency), (0, 1))


def fourth_word_matrix(
    frequencies: Frequency4, *, odd_multiplier: int = 1
) -> Matrix2:
    """Return the alternating fourfold word over the integers.

    The odd slots are multiplied by ``odd_multiplier``.  In
    Blomer--Pascadi this multiplier is an integral representative of
    ``a^{-1} (mod c)``.
    """

    inversion: Matrix2 = ((0, -1), (1, 0))
    word: Matrix2 = ((1, 0), (0, 1))
    for index, frequency in enumerate(frequencies):
        exponent = odd_multiplier * frequency if index % 2 == 0 else frequency
        word = _matrix_multiply(word, _translation(exponent))
        word = _matrix_multiply(word, inversion)
    return word


def fourth_trace_matrix(
    frequencies: Frequency4, *, odd_multiplier: int = 1
) -> int:
    """Trace of ``T^h1 S T^h2 S T^h3 S T^h4 S`` over the integers."""

    word = fourth_word_matrix(frequencies, odd_multiplier=odd_multiplier)
    return word[0][0] + word[1][1]


def fourth_trace_formula(
    frequencies: Frequency4, *, odd_multiplier: int = 1
) -> int:
    """Closed form of the fourfold trace word."""

    h1, h2, h3, h4 = frequencies
    return (
        odd_multiplier**2 * h1 * h2 * h3 * h4
        - odd_multiplier * (h1 + h3) * (h2 + h4)
        + 2
    )


def fourth_trace_discriminant(
    frequencies: Frequency4, *, odd_multiplier: int = 1
) -> int:
    """Quadratic discriminant ``tr(g)^2-4`` of the trace word."""

    trace = fourth_trace_formula(frequencies, odd_multiplier=odd_multiplier)
    return trace * trace - 4


def projective_level(
    frequencies: Frequency4, *, odd_multiplier: int = 1
) -> int:
    """Integral level of the fourfold word in ``PSL(2)``.

    For a non-scalar determinant-one matrix this is
    ``gcd(g01, g10, g00-g11)``.  Following the paper, the integral words
    ``+/-I`` have level zero because they are scalar modulo every modulus.
    """

    word = fourth_word_matrix(frequencies, odd_multiplier=odd_multiplier)
    if word in (((1, 0), (0, 1)), ((-1, 0), (0, -1))):
        return 0
    return gcd(
        gcd(abs(word[0][1]), abs(word[1][0])),
        abs(word[0][0] - word[1][1]),
    )


def scalar_congruence_roots(
    frequencies: Frequency4,
    modulus: int,
    *,
    odd_multiplier: int = 1,
) -> tuple[int, ...]:
    """Return all ``gamma`` with ``gamma^2=1`` and ``g=gamma I (mod d)``."""

    if modulus < 1:
        raise ValueError("the congruence modulus must be positive")
    word = fourth_word_matrix(frequencies, odd_multiplier=odd_multiplier)
    return tuple(
        gamma
        for gamma in range(modulus)
        if (gamma * gamma - 1) % modulus == 0
        and (word[0][0] - gamma) % modulus == 0
        and word[0][1] % modulus == 0
        and word[1][0] % modulus == 0
        and (word[1][1] - gamma) % modulus == 0
    )


def is_proposition_degenerate(frequencies: Frequency4) -> bool:
    """Exceptional strata explicitly split off in Proposition 3.6.

    For the orientation used in the paper these are
    ``h1*h2*h3=0`` or ``h1+h3=0``.  This is deliberately not replaced by
    the condition ``Delta=0``; the two exceptional notions differ.
    """

    h1, h2, h3, _ = frequencies
    return h1 * h2 * h3 == 0 or h1 + h3 == 0


def jacobi_symbol(value: int, odd_modulus: int) -> int:
    """Compute the Jacobi symbol ``(value/odd_modulus)`` exactly."""

    if odd_modulus < 1 or odd_modulus % 2 == 0:
        raise ValueError("Jacobi modulus must be a positive odd integer")
    value %= odd_modulus
    result = 1
    while value:
        while value % 2 == 0:
            value //= 2
            if odd_modulus % 8 in (3, 5):
                result = -result
        value, odd_modulus = odd_modulus, value
        if value % 4 == 3 and odd_modulus % 4 == 3:
            result = -result
        value %= odd_modulus
    return result if odd_modulus == 1 else 0


def _is_prime(value: int) -> bool:
    if value < 2:
        return False
    if value == 2:
        return True
    if value % 2 == 0:
        return False
    return all(value % divisor for divisor in range(3, isqrt(value) + 1, 2))


ProjectivePoint = int | None


def _projective_step(
    point: ProjectivePoint, frequency: int, prime: int
) -> ProjectivePoint:
    """Apply ``T^frequency S`` to a point of ``P^1(F_p)``."""

    if point is None:
        return frequency % prime
    if point == 0:
        return None
    return (frequency - pow(point, -1, prime)) % prime


def _projective_orbit(
    start: ProjectivePoint,
    frequencies: Frequency4,
    prime: int,
    *,
    odd_multiplier: int = 1,
) -> tuple[ProjectivePoint, ...]:
    orbit: list[ProjectivePoint] = [start]
    point = start
    for index, frequency in enumerate(frequencies):
        exponent = odd_multiplier * frequency if index % 2 == 0 else frequency
        point = _projective_step(point, exponent, prime)
        orbit.append(point)
    return tuple(orbit)


def projective_fixed_point_count(
    frequencies: Frequency4, prime: int, *, odd_multiplier: int = 1
) -> int:
    """Count fixed points of the trace word on ``P^1(F_p)``."""

    if not _is_prime(prime) or prime == 2:
        raise ValueError("the modulus must be an odd prime")
    points: tuple[ProjectivePoint, ...] = tuple(range(prime)) + (None,)
    return sum(
        _projective_orbit(
            point, frequencies, prime, odd_multiplier=odd_multiplier
        )[-1]
        == point
        for point in points
    )


def admissible_projective_cycle_count(
    frequencies: Frequency4, prime: int, *, odd_multiplier: int = 1
) -> int:
    """Count fixed projective orbits that never meet ``0`` or infinity."""

    if not _is_prime(prime) or prime == 2:
        raise ValueError("the modulus must be an odd prime")
    count = 0
    for point in range(1, prime):
        orbit = _projective_orbit(
            point, frequencies, prime, odd_multiplier=odd_multiplier
        )
        if orbit[-1] == point and all(
            entry is not None and entry != 0 for entry in orbit
        ):
            count += 1
    return count


def representation_character_prime(
    frequencies: Frequency4, prime: int, *, odd_multiplier: int = 1
) -> int:
    """Evaluate the special representation character at the trace word.

    This is the exact prime-modulus dichotomy in Blomer--Pascadi,
    equation (3.11): scalar ``+/-I`` words have value ``p``; all other
    words have value ``(tr(g)^2-4)/p``.
    """

    if not _is_prime(prime) or prime == 2:
        raise ValueError("the modulus must be an odd prime")
    word = fourth_word_matrix(frequencies, odd_multiplier=odd_multiplier)
    reduced = tuple(tuple(entry % prime for entry in row) for row in word)
    identity = ((1, 0), (0, 1))
    negative_identity = ((prime - 1, 0), (0, prime - 1))
    if reduced in (identity, negative_identity):
        return prime
    return jacobi_symbol(
        fourth_trace_discriminant(
            frequencies, odd_multiplier=odd_multiplier
        ),
        prime,
    )


def inverse_cycle_solution_count(
    frequencies: Frequency4, odd_prime: int
) -> int:
    """Count the naive cyclic inverse equations over ``F_p^*``.

    The equations are ``x_j + x_{j-1}^{-1} = h_j`` cyclically.  This
    finite count is included to falsify a tempting shortcut: it is not, in
    general, the representation-character expression ``1+(Delta/p)``.
    """

    if not _is_prime(odd_prime) or odd_prime == 2:
        raise ValueError("the finite-field modulus must be an odd prime")
    count = 0
    for variables in product(range(1, odd_prime), repeat=4):
        if all(
            (
                variables[index]
                + pow(variables[index - 1], -1, odd_prime)
                - frequencies[index]
            )
            % odd_prime
            == 0
            for index in range(4)
        ):
            count += 1
    return count


def discriminant_multiplicities(
    height: int, *, exclude_degenerate: bool = False
) -> Counter[int]:
    """Multiplicity table for nonzero signed frequencies ``|h_j|<=height``."""

    if height < 1:
        raise ValueError("height must be positive")
    signed = tuple(range(-height, 0)) + tuple(range(1, height + 1))
    result: Counter[int] = Counter()
    for raw_frequencies in product(signed, repeat=4):
        frequencies: Frequency4 = (
            raw_frequencies[0],
            raw_frequencies[1],
            raw_frequencies[2],
            raw_frequencies[3],
        )
        if exclude_degenerate and is_proposition_degenerate(frequencies):
            continue
        result[fourth_trace_discriminant(frequencies)] += 1
    return result


def multiplicity_energy(multiplicities: Mapping[int, int]) -> int:
    """Return ``sum_D multiplicity(D)^2`` for a finite trace family."""

    if any(value < 0 for value in multiplicities.values()):
        raise ValueError("multiplicities must be nonnegative")
    return sum(value * value for value in multiplicities.values())
