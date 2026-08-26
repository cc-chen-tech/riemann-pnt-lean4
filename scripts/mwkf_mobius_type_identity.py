#!/usr/bin/env python3
"""Finite checks for the exact Möbius Type-I/II decomposition."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from fractions import Fraction
from math import gcd, isqrt


@dataclass(frozen=True)
class CenteredResonanceCoordinates:
    j: int
    w: int

    @property
    def linear_slope(self) -> int:
        return self.j + 1

    @property
    def distance(self) -> int:
        return abs(self.w)


@dataclass(frozen=True)
class RestrictedMobiusLogSignature:
    mobius_mass: int
    negative_log_prime_coefficients: tuple[tuple[int, int], ...]


@dataclass(frozen=True)
class TwistedRestrictedMobiusLogSignature:
    twisted_mobius_mass: Fraction
    negative_log_prime_coefficients: tuple[tuple[int, Fraction], ...]


@dataclass(frozen=True)
class BalancedSelbergReflection:
    direct: Fraction
    completed_prime_part: Fraction
    negative_reflected_tail: Fraction
    reflected_cofactors: tuple[int, ...]


@dataclass(frozen=True)
class ReflectedPairKernelEnergy:
    direct_truncated: Fraction
    completed_completed: Fraction
    completed_reflected: Fraction
    reflected_completed: Fraction
    reflected_reflected: Fraction
    expanded: Fraction


@dataclass(frozen=True)
class ReflectedBoundaryDiagonal:
    direct: Fraction
    lcm_sum: Fraction
    gcd_parameterized_sum: Fraction
    active_gcd_coordinates: tuple[tuple[int, int, int], ...]


@dataclass(frozen=True)
class ReflectedBoundaryPairKernel:
    direct: Fraction
    unfolded: Fraction
    active_factor_pairs: tuple[tuple[int, int, int, int], ...]


@dataclass(frozen=True)
class SecondaryZeroPacket:
    afe_direction: str
    poisson_frequency_h: int
    additive_shift_delta: int
    dyadic_label: str
    pair_kernel: dict[tuple[int, int], Fraction]


@dataclass(frozen=True)
class ZeroFrequencyReflectedMaster:
    packet_contributions: tuple[tuple[str, int, int, str, Fraction], ...]
    afe_direction_contributions: tuple[tuple[str, Fraction], ...]
    direct_full_remainder: Fraction
    completed_completed: Fraction
    completed_reflected: Fraction
    reflected_completed: Fraction
    reflected_reflected: Fraction
    explicit_diagonal: Fraction
    reflected_unfolded: Fraction
    resonant_row_component: Fraction
    resonant_column_component: Fraction
    resonant_grand_component: Fraction
    resonant_reflected_projection: Fraction
    resonant_master_term: Fraction
    centered_remainder: Fraction
    recombined_master_remainder: Fraction
    weighted_centered_row_sums: tuple[tuple[int, Fraction], ...]
    weighted_centered_column_sums: tuple[tuple[int, Fraction], ...]
    centered_kernel_entries: tuple[tuple[int, int, Fraction], ...]


@dataclass(frozen=True)
class CenteredOperatorSavingLedger:
    raw_sum_exponent: Fraction
    target_sum_exponent: Fraction
    required_operator_saving_exponent: Fraction
    required_ttstar_saving_exponent: Fraction
    fixed_coefficient_operator_gate_is_sufficient: bool
    uniform_unit_ball_operator_gate_is_equivalent: bool


@dataclass(frozen=True)
class CoupledOperatorRow:
    label: str
    short_slope_k: int
    short_slope_l: int


@dataclass(frozen=True)
class CoupledTTStarDeterminantSplit:
    direct_quadratic: Fraction
    gram_quadratic: Fraction
    determinant_zero_quadratic: Fraction
    determinant_nonzero_quadratic: Fraction
    determinant_zero_pairs: tuple[tuple[str, str], ...]
    determinant_nonzero_pairs: tuple[tuple[str, str], ...]
    gram_entries: tuple[tuple[str, str, Fraction], ...]


@dataclass(frozen=True)
class CoprimeDivisorPairIdentity:
    direct_coprime_sum: Fraction
    mobius_inverted_sum: Fraction
    active_common_divisors: tuple[int, ...]


@dataclass(frozen=True)
class ProportionalDiagonalCoordinates:
    sign: int
    common_n_factor: int
    primitive_n1: int
    primitive_n2: int
    common_y_factor: int


@dataclass(frozen=True)
class RestrictedZeroRayPairConvolution:
    u: int
    v: int
    k: int
    cutoff_u: int
    left_product: int
    right_product: int
    left_sector_sum: int
    right_sector_sum: int
    pair_sector_product: int
    squarefree_ray_support: bool
    common_k_mobius_cancels_exactly: bool


@dataclass(frozen=True)
class MobiusUnsignedSectorRecombination:
    n: int
    cutoff_u: int
    mobius_value: int
    pure_unsigned_outer_product: int
    pure_unsigned_contribution: int
    nontrivial_signed_contribution: int
    recombined_contribution: int
    outer_contributions: tuple[tuple[int, int], ...]
    recombination_identity_verified: bool


@dataclass(frozen=True)
class FourMobiusUnsignedSectorRecombination:
    values: tuple[int, int, int, int]
    cutoff_u: int
    recombined_mobius_product: int
    pure_unsigned_bblr_box_contribution: int
    all_other_boxes_contribution: int
    pure_box_is_unweighted_and_positive: bool
    recombination_identity_verified: bool


@dataclass(frozen=True)
class ZeroRayPhaseReduction:
    s_u: int
    a_u: int
    s_k: int
    a_k: int
    original_fixed_phase: Fraction
    reduced_fixed_phase: Fraction
    original_real_phase: Fraction
    product_real_phase: Fraction
    original_common_b_phase: Fraction
    product_common_b_phase: Fraction
    primitive_slope_removed_from_reciprocal_phase: bool


@dataclass(frozen=True)
class CommonBPhaseReciprocity:
    determinant: int
    original_phase: Fraction
    determinant_phase: Fraction
    smooth_real_phase: Fraction
    dual_reciprocal_phase: Fraction
    reciprocal_completed_phase: Fraction
    b_divides_determinant: bool


@dataclass(frozen=True)
class LcmBPhaseCompression:
    lcm_modulus: int
    compressed_numerator: int
    original_phase: Fraction
    compressed_phase: Fraction


@dataclass(frozen=True)
class DeterminantLineCoordinates:
    gcd_j_v: int
    primitive_j: int
    primitive_v: int
    shift_quotient: int
    particular_r: int
    particular_s: int

    def solution(self, n: int) -> tuple[int, int]:
        return (
            self.particular_r + self.primitive_j * n,
            self.particular_s + self.primitive_v * n,
        )


@dataclass(frozen=True)
class DeterminantSlopeSquareCoordinates:
    shift1: int
    shift2: int
    cross_determinant: int
    recovered_primitive_j: int | None
    recovered_primitive_v: int | None
    zero_determinant_is_identity_diagonal: bool


@dataclass(frozen=True)
class DeterminantCokernelCoordinates:
    modulus: int
    smith_first_invariant: int
    smith_second_invariant: int
    admissible_shift_residues: tuple[tuple[int, int], ...]
    annihilator_characters: tuple[tuple[int, int], ...]
    cokernel_is_cyclic: bool


def proportional_diagonal_coordinates(
    *,
    n1: int,
    y1: int,
    n2: int,
    y2: int,
) -> ProportionalDiagonalCoordinates:
    """Parameterize exactly the zero complementary-divisor equation.

    For nonzero signed ``n_i`` and positive ``y_i``, the equation
    ``n1*y2=n2*y1`` forces the signs of ``n1,n2`` to agree.  Writing
    ``|n1|=g*u`` and ``|n2|=g*v`` with ``(u,v)=1`` then gives uniquely
    ``y1=u*k`` and ``y2=v*k``.
    """
    if n1 == 0 or n2 == 0 or y1 <= 0 or y2 <= 0:
        raise ValueError("require nonzero n_i and positive y_i")
    if n1 * y2 != n2 * y1:
        raise ValueError("not on the zero-complementary ray")

    common_n_factor = gcd(abs(n1), abs(n2))
    primitive_n1 = abs(n1) // common_n_factor
    primitive_n2 = abs(n2) // common_n_factor
    if y1 % primitive_n1 != 0 or y2 % primitive_n2 != 0:
        raise AssertionError("primitive proportionality divisibility failed")
    common_y_factor = y1 // primitive_n1
    if y2 // primitive_n2 != common_y_factor:
        raise AssertionError("primitive proportionality factor mismatch")

    return ProportionalDiagonalCoordinates(
        sign=1 if n1 > 0 else -1,
        common_n_factor=common_n_factor,
        primitive_n1=primitive_n1,
        primitive_n2=primitive_n2,
        common_y_factor=common_y_factor,
    )


def centered_resonance_coordinates(
    *,
    r: int,
    s: int,
) -> CenteredResonanceCoordinates:
    """Write ``r-s=j*s+w`` with the unique ``-s/2 < w <= s/2``.

    The positive representative is selected at an even-modulus tie.  Thus
    ``r=(j+1)*s+w`` and every integer product frequency satisfies
    ``a*r == a*w (mod s)`` without evaluating an exponential.
    """
    if r <= 0 or s <= 0:
        raise ValueError("require r,s > 0")
    difference = r - s
    w = difference % s
    if 2 * w > s:
        w -= s
    numerator = difference - w
    assert numerator % s == 0
    return CenteredResonanceCoordinates(j=numerator // s, w=w)


def _restricted_mobius(n: int, modulus: int) -> int:
    """Return ``mu(n)`` restricted to integers coprime to ``modulus``."""
    return mobius(n) if gcd(n, modulus) == 1 else 0


def coprime_centered_mobius_reindex(
    *,
    s: int,
    w: int,
    slope: int,
    q: int,
) -> int:
    """Evaluate the exact common-divisor reindexing of a centered pair.

    Put ``r=slope*s+w`` and ``mu_Q(n)=mu(n) 1_(n,Q)=1``.  Möbius
    inversion of ``(s,w)=1`` gives

    ``mu_q(s) mu_q(r) 1_(s,w)=1``
    `` = sum_{d|(s,w), (d,q)=1} mu(d)``
    ``     * mu_{qd}(s/d) mu_{qd}(slope*s/d+w/d)``.

    The return value is the right-hand side.  This finite helper checks
    the reindexing only; it makes no estimate for the resulting sums.
    """
    if s <= 0 or slope <= 0 or q <= 0:
        raise ValueError("require s, slope, q > 0")
    r = slope * s + w
    if r <= 0:
        raise ValueError("require slope*s+w > 0")

    total = 0
    common_divisor = gcd(s, abs(w))
    for d in divisors(common_divisor):
        coefficient = mobius(d)
        if coefficient == 0 or gcd(d, q) != 1:
            continue
        n = s // d
        shift = w // d
        restricted_modulus = q * d
        total += (
            coefficient
            * _restricted_mobius(n, restricted_modulus)
            * _restricted_mobius(
                slope * n + shift,
                restricted_modulus,
            )
        )
    return total


def mobius(n: int) -> int:
    if n < 1:
        raise ValueError("n must be positive")
    value = n
    primes = 0
    p = 2
    while p * p <= value:
        if value % p == 0:
            value //= p
            primes += 1
            if value % p == 0:
                return 0
            while value % p == 0:
                value //= p
        p += 1
    if value > 1:
        primes += 1
    return -1 if primes % 2 else 1


def divisors(n: int) -> tuple[int, ...]:
    small: list[int] = []
    large: list[int] = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            small.append(d)
            if d * d != n:
                large.append(n // d)
    return tuple(small + list(reversed(large)))


def _distinct_prime_factors(n: int) -> tuple[int, ...]:
    if n <= 0:
        raise ValueError("factorization input must be positive")
    factors: list[int] = []
    candidate = 2
    remainder = n
    while candidate * candidate <= remainder:
        if remainder % candidate == 0:
            factors.append(candidate)
            while remainder % candidate == 0:
                remainder //= candidate
        candidate += 1
    if remainder > 1:
        factors.append(remainder)
    return tuple(factors)


def endpoint_q_density(n: int) -> Fraction:
    """Return ``prod_(p|n) (1+1/p)^-1`` exactly."""
    density = Fraction(1)
    for prime in _distinct_prime_factors(n):
        density *= Fraction(prime, prime + 1)
    return density


def endpoint_density_convolution_coefficient(n: int) -> Fraction:
    """Coefficient ``h(n)`` in ``mu(n)*g(n)=(mu*h)(n)``.

    The local factor is ``h(1)=1`` and
    ``h(p^a)=1/(p+1)`` for every prime power with ``a>=1``.  Hence
    ``sum |h(n)| n^-sigma`` converges for every ``sigma>0``.
    """
    coefficient = Fraction(1)
    for prime in _distinct_prime_factors(n):
        coefficient *= Fraction(1, prime + 1)
    return coefficient


def endpoint_weighted_mobius(n: int) -> Fraction:
    """The fixed multiplicative weight left after endpoint q-summation."""
    if n <= 0:
        raise ValueError("endpoint weighted Mobius input must be positive")
    return Fraction(mobius(n)) * endpoint_q_density(n)


def q_free_part(n: int, q: int) -> int:
    """Remove from ``n`` every prime-power factor supported on ``q``."""
    if n <= 0 or q <= 0:
        raise ValueError("q-free-part inputs must be positive")
    result = n
    for prime in _distinct_prime_factors(q):
        while result % prime == 0:
            result //= prime
    return result


def q_restricted_mobius_log_signature(
    n: int,
    q: int,
) -> RestrictedMobiusLogSignature:
    """Formal coefficients of the complete q-restricted tapered divisor sum.

    The represented expression is

    ``log(X) * sum mu(d) - sum mu(d) log(d)``, over divisors ``d|n``
    coprime to ``q``.  Logarithms of distinct primes are retained as exact
    formal basis elements.
    """
    if n <= 0 or q <= 0:
        raise ValueError("restricted divisor inputs must be positive")
    restricted = tuple(d for d in divisors(n) if gcd(d, q) == 1)
    mass = sum(mobius(d) for d in restricted)
    coefficients: list[tuple[int, int]] = []
    for prime in _distinct_prime_factors(n):
        coefficient = 0
        for divisor in restricted:
            valuation = 0
            remainder = divisor
            while remainder % prime == 0:
                valuation += 1
                remainder //= prime
            coefficient -= mobius(divisor) * valuation
        if coefficient:
            coefficients.append((prime, coefficient))
    return RestrictedMobiusLogSignature(
        mobius_mass=mass,
        negative_log_prime_coefficients=tuple(coefficients),
    )


def truncated_selberg_divisor_sides(
    n: int,
    *,
    cutoff: int,
    normalization: Fraction,
    prime_log_weights: dict[int, Fraction],
) -> tuple[Fraction, Fraction, Fraction]:
    """Finite forms of the truncated tapered Möbius divisor identity.

    ``prime_log_weights`` defines a completely additive formal logarithm;
    an unspecified prime ``p`` has weight ``p``.  The three returned values
    are respectively the truncated divisor sum, the completed full divisor
    sum minus its ``d > cutoff`` tail, and the same tail after ``d=n/k``.
    """
    if n <= 0 or cutoff <= 0:
        raise ValueError("Selberg divisor inputs must be positive")
    normalization = Fraction(normalization)
    if normalization == 0:
        raise ValueError("Selberg normalization must be nonzero")

    def formal_log(value: int) -> Fraction:
        result = Fraction(0)
        remainder = value
        for prime in _distinct_prime_factors(value):
            valuation = 0
            while remainder % prime == 0:
                valuation += 1
                remainder //= prime
            result += valuation * prime_log_weights.get(prime, Fraction(prime))
        return result

    def taper(divisor: int) -> Fraction:
        return Fraction(1) - formal_log(divisor) / normalization

    direct = sum(
        (Fraction(mobius(divisor)) * taper(divisor) for divisor in divisors(n)
         if divisor <= cutoff),
        Fraction(0),
    )
    prime_factors = _distinct_prime_factors(n)
    generalized_von_mangoldt = (
        formal_log(prime_factors[0]) if len(prime_factors) == 1 else Fraction(0)
    )
    full = (
        (Fraction(1) if n == 1 else Fraction(0))
        + generalized_von_mangoldt / normalization
    )
    completed = full - sum(
        (Fraction(mobius(divisor)) * taper(divisor) for divisor in divisors(n)
         if divisor > cutoff),
        Fraction(0),
    )
    reflected = full - sum(
        (
            Fraction(mobius(n // cofactor)) * taper(n // cofactor)
            for cofactor in divisors(n)
            if cofactor * cutoff < n
        ),
        Fraction(0),
    )
    return direct, completed, reflected


def balanced_selberg_reflection_sides(
    *,
    divisor: int,
    cofactor: int,
    cutoff: int,
    normalization: Fraction,
    prime_log_weights: dict[int, Fraction],
) -> BalancedSelbergReflection:
    """Exact zero-mode reflection on a balanced squarefree product.

    The hypotheses ``1 < cofactor < divisor <= cutoff`` and
    ``mobius(divisor) != 0`` force ``divisor * cofactor`` to have at
    least two distinct prime factors.  Hence its completed divisor sum
    has no von-Mangoldt part.  Every reflected cofactor ``k`` obeys the
    strict descent ``k < cofactor`` because ``k*cutoff < divisor*cofactor``.
    """
    if not 1 < cofactor < divisor <= cutoff:
        raise ValueError("require 1 < cofactor < divisor <= cutoff")
    if mobius(divisor) == 0:
        raise ValueError("the balanced divisor must be squarefree")

    product = divisor * cofactor
    direct, _, reflected = truncated_selberg_divisor_sides(
        product,
        cutoff=cutoff,
        normalization=normalization,
        prime_log_weights=prime_log_weights,
    )
    reflected_cofactors = tuple(
        k for k in divisors(product) if k * cutoff < product
    )
    completed_prime_part = Fraction(0)
    return BalancedSelbergReflection(
        direct=direct,
        completed_prime_part=completed_prime_part,
        negative_reflected_tail=reflected - completed_prime_part,
        reflected_cofactors=reflected_cofactors,
    )


def reflected_pair_kernel_energy_sides(
    *,
    completed_coefficients: dict[int, Fraction],
    reflected_coefficients: dict[int, Fraction],
    pair_kernel: dict[tuple[int, int], Fraction],
) -> ReflectedPairKernelEnergy:
    """Expand ``B=F-R`` against an arbitrary finite pair kernel."""
    support = tuple(
        sorted(set(completed_coefficients) | set(reflected_coefficients))
    )
    if any(index <= 0 for index in support):
        raise ValueError("pair-kernel coefficient indices must be positive")

    def coefficient(
        coefficients: dict[int, Fraction], index: int
    ) -> Fraction:
        return Fraction(coefficients.get(index, Fraction(0)))

    def pair_sum(
        left: dict[int, Fraction], right: dict[int, Fraction]
    ) -> Fraction:
        return sum(
            (
                Fraction(pair_kernel.get((x, y), Fraction(0)))
                * coefficient(left, x)
                * coefficient(right, y)
                for x in support
                for y in support
            ),
            Fraction(0),
        )

    truncated = {
        index: coefficient(completed_coefficients, index)
        - coefficient(reflected_coefficients, index)
        for index in support
    }
    direct_truncated = pair_sum(truncated, truncated)
    completed_completed = pair_sum(
        completed_coefficients, completed_coefficients
    )
    completed_reflected = pair_sum(
        completed_coefficients, reflected_coefficients
    )
    reflected_completed = pair_sum(
        reflected_coefficients, completed_coefficients
    )
    reflected_reflected = pair_sum(
        reflected_coefficients, reflected_coefficients
    )
    expanded = (
        completed_completed
        - completed_reflected
        - reflected_completed
        + reflected_reflected
    )
    return ReflectedPairKernelEnergy(
        direct_truncated=direct_truncated,
        completed_completed=completed_completed,
        completed_reflected=completed_reflected,
        reflected_completed=reflected_completed,
        reflected_reflected=reflected_reflected,
        expanded=expanded,
    )


def reflected_boundary_diagonal_sides(
    *,
    long_weights: dict[int, Fraction],
    cutoff: int,
    product_cutoff: int,
) -> ReflectedBoundaryDiagonal:
    """Diagonal reflected energy in direct, LCM, and gcd coordinates."""
    if cutoff <= 0 or product_cutoff <= 0:
        raise ValueError("boundary cutoffs must be positive")
    if any(index <= cutoff for index in long_weights):
        raise ValueError("all reflected divisors must exceed the cutoff")
    if any(mobius(index) == 0 for index in long_weights):
        raise ValueError("reflected divisors must be squarefree")

    weights = {
        index: Fraction(weight) for index, weight in long_weights.items()
    }
    direct = sum(
        (
            sum(
                (
                    weight
                    for divisor, weight in weights.items()
                    if product % divisor == 0
                ),
                Fraction(0),
            )
            ** 2
            for product in range(1, product_cutoff + 1)
        ),
        Fraction(0),
    )

    lcm_sum = Fraction(0)
    gcd_parameterized_sum = Fraction(0)
    active_coordinates: list[tuple[int, int, int]] = []
    for left_divisor, left_weight in weights.items():
        for right_divisor, right_weight in weights.items():
            common = gcd(left_divisor, right_divisor)
            left = left_divisor // common
            right = right_divisor // common
            multiple_count = product_cutoff // (common * left * right)
            contribution = left_weight * right_weight * multiple_count
            lcm_sum += contribution
            gcd_parameterized_sum += contribution
            if contribution:
                active_coordinates.append((common, left, right))

    return ReflectedBoundaryDiagonal(
        direct=direct,
        lcm_sum=lcm_sum,
        gcd_parameterized_sum=gcd_parameterized_sum,
        active_gcd_coordinates=tuple(active_coordinates),
    )


def reflected_boundary_pair_kernel_sides(
    *,
    long_weights: dict[int, Fraction],
    cutoff: int,
    product_cutoff: int,
    pair_kernel: dict[tuple[int, int], Fraction],
) -> ReflectedBoundaryPairKernel:
    """Unfold a reflected pair energy into its two short cofactors."""
    if cutoff <= 0 or product_cutoff <= 0:
        raise ValueError("boundary cutoffs must be positive")
    if any(index <= cutoff for index in long_weights):
        raise ValueError("all reflected divisors must exceed the cutoff")
    if any(mobius(index) == 0 for index in long_weights):
        raise ValueError("reflected divisors must be squarefree")

    weights = {
        index: Fraction(weight) for index, weight in long_weights.items()
    }

    def reflected_coefficient(product: int) -> Fraction:
        return sum(
            (
                weight
                for divisor, weight in weights.items()
                if product % divisor == 0
            ),
            Fraction(0),
        )

    direct = sum(
        (
            Fraction(kernel_weight)
            * reflected_coefficient(left_product)
            * reflected_coefficient(right_product)
            for (left_product, right_product), kernel_weight in (
                pair_kernel.items()
            )
            if 1 <= left_product <= product_cutoff
            and 1 <= right_product <= product_cutoff
        ),
        Fraction(0),
    )

    unfolded = Fraction(0)
    active_factor_pairs: list[tuple[int, int, int, int]] = []
    for left_divisor, left_weight in weights.items():
        for right_divisor, right_weight in weights.items():
            for left_cofactor in range(
                1, product_cutoff // left_divisor + 1
            ):
                for right_cofactor in range(
                    1, product_cutoff // right_divisor + 1
                ):
                    kernel_weight = Fraction(
                        pair_kernel.get(
                            (
                                left_divisor * left_cofactor,
                                right_divisor * right_cofactor,
                            ),
                            Fraction(0),
                        )
                    )
                    contribution = (
                        left_weight * right_weight * kernel_weight
                    )
                    unfolded += contribution
                    if contribution:
                        active_factor_pairs.append(
                            (
                                left_divisor,
                                left_cofactor,
                                right_divisor,
                                right_cofactor,
                            )
                        )

    return ReflectedBoundaryPairKernel(
        direct=direct,
        unfolded=unfolded,
        active_factor_pairs=tuple(active_factor_pairs),
    )


def zero_frequency_reflected_master_sides(
    *,
    completed_coefficients: dict[int, Fraction],
    long_left_weights: dict[int, Fraction],
    long_right_weights: dict[int, Fraction],
    product_cutoff: int,
    secondary_zero_packets: tuple[SecondaryZeroPacket, ...],
    explicit_diagonal_weights: dict[int, Fraction],
    left_density_weights: dict[int, Fraction],
    right_density_weights: dict[int, Fraction],
) -> ZeroFrequencyReflectedMaster:
    """One finite zero-frequency master identity before any outer Cauchy.

    Every secondary-zero packet keeps its AFE direction, nonzero original
    Poisson frequency, unrestricted additive shift, dyadic label, and full
    smooth pair kernel.
    The kernels are summed without taking absolute values.  For ``B=F-R``
    the pair energy is then expanded into its two distinct cross terms.
    The reflected ``D,E`` cofactor kernel is double-centered once against
    the supplied probability weights.  Its row/column/grand projections,
    together with the completed terms and the explicit diagonal, form the
    resonant master term; only the zero-row, zero-column operator remains
    in ``centered_remainder``.

    The original Poisson ``h=0`` term is rejected: it is already combined
    with the explicit diagonal in equations (4.6)--(4.8) of the note.
    """

    if product_cutoff <= 0:
        raise ValueError("product cutoff must be positive")
    if not secondary_zero_packets:
        raise ValueError("at least one secondary-zero packet is required")
    if any(
        packet.poisson_frequency_h == 0
        for packet in secondary_zero_packets
    ):
        raise ValueError("the original h=0 mode is already counted in (4.6)--(4.8)")
    if any(not packet.afe_direction for packet in secondary_zero_packets):
        raise ValueError("every AFE direction must be named")
    if any(not packet.dyadic_label for packet in secondary_zero_packets):
        raise ValueError("every dyadic packet must be named")
    left_divisors = tuple(sorted(long_left_weights))
    right_divisors = tuple(sorted(long_right_weights))
    if not left_divisors or not right_divisors:
        raise ValueError("both reflected divisor families must be nonempty")
    if set(left_density_weights) != set(left_divisors):
        raise ValueError("left density support must equal the left divisor support")
    if set(right_density_weights) != set(right_divisors):
        raise ValueError("right density support must equal the right divisor support")

    left_density = {
        index: Fraction(left_density_weights[index]) for index in left_divisors
    }
    right_density = {
        index: Fraction(right_density_weights[index])
        for index in right_divisors
    }
    if any(weight < 0 for weight in left_density.values()) or any(
        weight < 0 for weight in right_density.values()
    ):
        raise ValueError("density weights must be nonnegative")
    if sum(left_density.values(), Fraction(0)) != 1:
        raise ValueError("left density weights must sum to one")
    if sum(right_density.values(), Fraction(0)) != 1:
        raise ValueError("right density weights must sum to one")

    for packet in secondary_zero_packets:
        kernel = packet.pair_kernel
        if any(
            x <= 0 or y <= 0 or x > product_cutoff or y > product_cutoff
            for x, y in kernel
        ):
            raise ValueError("AFE kernel indices must lie in the product box")
    if any(
        index <= 0 or index > product_cutoff
        for index in explicit_diagonal_weights
    ):
        raise ValueError("diagonal indices must lie in the product box")

    completed = {
        index: Fraction(completed_coefficients.get(index, Fraction(0)))
        for index in range(1, product_cutoff + 1)
    }
    left_long = {
        index: Fraction(long_left_weights[index]) for index in left_divisors
    }
    right_long = {
        index: Fraction(long_right_weights[index]) for index in right_divisors
    }

    def reflected(product: int, weights: dict[int, Fraction]) -> Fraction:
        return sum(
            (
                weight
                for divisor, weight in weights.items()
                if product % divisor == 0
            ),
            Fraction(0),
        )

    reflected_left = {
        x: reflected(x, left_long) for x in range(1, product_cutoff + 1)
    }
    reflected_right = {
        y: reflected(y, right_long) for y in range(1, product_cutoff + 1)
    }
    truncated_left = {
        x: completed[x] - reflected_left[x]
        for x in range(1, product_cutoff + 1)
    }
    truncated_right = {
        y: completed[y] - reflected_right[y]
        for y in range(1, product_cutoff + 1)
    }

    combined_kernel: dict[tuple[int, int], Fraction] = {}
    for packet in secondary_zero_packets:
        kernel = packet.pair_kernel
        for pair, weight in kernel.items():
            combined_kernel[pair] = (
                combined_kernel.get(pair, Fraction(0)) + Fraction(weight)
            )

    def pair_sum(
        kernel: dict[tuple[int, int], Fraction],
        left: dict[int, Fraction],
        right: dict[int, Fraction],
    ) -> Fraction:
        return sum(
            (
                Fraction(weight) * left[x] * right[y]
                for (x, y), weight in kernel.items()
            ),
            Fraction(0),
        )

    packet_contributions = tuple(
        (
            packet.afe_direction,
            packet.poisson_frequency_h,
            packet.additive_shift_delta,
            packet.dyadic_label,
            pair_sum(packet.pair_kernel, truncated_left, truncated_right),
        )
        for packet in secondary_zero_packets
    )
    direction_order = tuple(
        dict.fromkeys(packet.afe_direction for packet in secondary_zero_packets)
    )
    direction_contributions = tuple(
        (
            direction,
            sum(
                (
                    contribution
                    for packet_direction, _, _, _, contribution in (
                        packet_contributions
                    )
                    if packet_direction == direction
                ),
                Fraction(0),
            ),
        )
        for direction in direction_order
    )
    pair_energy = sum(
        (contribution for _, _, _, _, contribution in packet_contributions),
        Fraction(0),
    )
    explicit_diagonal = sum(
        (
            Fraction(weight) * truncated_left[index] * truncated_right[index]
            for index, weight in explicit_diagonal_weights.items()
        ),
        Fraction(0),
    )
    completed_completed = pair_sum(combined_kernel, completed, completed)
    completed_reflected = pair_sum(
        combined_kernel, completed, reflected_right
    )
    reflected_completed = pair_sum(
        combined_kernel, reflected_left, completed
    )
    reflected_reflected = pair_sum(
        combined_kernel, reflected_left, reflected_right
    )

    boundary_kernel: dict[tuple[int, int], Fraction] = {}
    for left_divisor in left_divisors:
        for right_divisor in right_divisors:
            boundary_kernel[(left_divisor, right_divisor)] = sum(
                (
                    combined_kernel.get(
                        (left_divisor * left_cofactor,
                         right_divisor * right_cofactor),
                        Fraction(0),
                    )
                    for left_cofactor in range(
                        1, product_cutoff // left_divisor + 1
                    )
                    for right_cofactor in range(
                        1, product_cutoff // right_divisor + 1
                    )
                ),
                Fraction(0),
            )

    reflected_unfolded = sum(
        (
            left_long[left] * right_long[right] * value
            for (left, right), value in boundary_kernel.items()
        ),
        Fraction(0),
    )
    row_means = {
        left: sum(
            (
                right_density[right] * boundary_kernel[(left, right)]
                for right in right_divisors
            ),
            Fraction(0),
        )
        for left in left_divisors
    }
    column_means = {
        right: sum(
            (
                left_density[left] * boundary_kernel[(left, right)]
                for left in left_divisors
            ),
            Fraction(0),
        )
        for right in right_divisors
    }
    grand_mean = sum(
        (left_density[left] * row_means[left] for left in left_divisors),
        Fraction(0),
    )
    centered_kernel = {
        (left, right): (
            boundary_kernel[(left, right)]
            - row_means[left]
            - column_means[right]
            + grand_mean
        )
        for left in left_divisors
        for right in right_divisors
    }
    weighted_row_sums = tuple(
        (
            left,
            sum(
                (
                    right_density[right] * centered_kernel[(left, right)]
                    for right in right_divisors
                ),
                Fraction(0),
            ),
        )
        for left in left_divisors
    )
    weighted_column_sums = tuple(
        (
            right,
            sum(
                (
                    left_density[left] * centered_kernel[(left, right)]
                    for left in left_divisors
                ),
                Fraction(0),
            ),
        )
        for right in right_divisors
    )
    centered_remainder = sum(
        (
            left_long[left]
            * right_long[right]
            * centered_kernel[(left, right)]
            for left in left_divisors
            for right in right_divisors
        ),
        Fraction(0),
    )
    left_mass = sum(left_long.values(), Fraction(0))
    right_mass = sum(right_long.values(), Fraction(0))
    resonant_row_component = right_mass * sum(
        (left_long[left] * row_means[left] for left in left_divisors),
        Fraction(0),
    )
    resonant_column_component = left_mass * sum(
        (right_long[right] * column_means[right] for right in right_divisors),
        Fraction(0),
    )
    resonant_grand_component = -grand_mean * left_mass * right_mass
    resonant_projection = (
        resonant_row_component
        + resonant_column_component
        + resonant_grand_component
    )
    resonant_master = (
        completed_completed
        - completed_reflected
        - reflected_completed
        + resonant_projection
        - explicit_diagonal
    )
    recombined = resonant_master + centered_remainder
    return ZeroFrequencyReflectedMaster(
        packet_contributions=packet_contributions,
        afe_direction_contributions=direction_contributions,
        direct_full_remainder=pair_energy - explicit_diagonal,
        completed_completed=completed_completed,
        completed_reflected=completed_reflected,
        reflected_completed=reflected_completed,
        reflected_reflected=reflected_reflected,
        explicit_diagonal=explicit_diagonal,
        reflected_unfolded=reflected_unfolded,
        resonant_row_component=resonant_row_component,
        resonant_column_component=resonant_column_component,
        resonant_grand_component=resonant_grand_component,
        resonant_reflected_projection=resonant_projection,
        resonant_master_term=resonant_master,
        centered_remainder=centered_remainder,
        recombined_master_remainder=recombined,
        weighted_centered_row_sums=weighted_row_sums,
        weighted_centered_column_sums=weighted_column_sums,
        centered_kernel_entries=tuple(
            (left, right, centered_kernel[(left, right)])
            for left in left_divisors
            for right in right_divisors
        ),
    )


def centered_operator_saving_ledger(
    *,
    raw_sum_exponent: Fraction,
    target_sum_exponent: Fraction,
) -> CenteredOperatorSavingLedger:
    """Record the exact norm saving demanded by a centered-operator gate.

    A fixed-coefficient ``2 -> 2`` estimate is sufficient by Cauchy.  The
    same estimate is equivalent to a bilinear bound only when required
    uniformly over both Euclidean unit balls.  Squaring through ``TT*``
    doubles the exponent saving.
    """

    raw = Fraction(raw_sum_exponent)
    target = Fraction(target_sum_exponent)
    if target > raw:
        raise ValueError("the target exponent cannot exceed the raw exponent")
    saving = raw - target
    return CenteredOperatorSavingLedger(
        raw_sum_exponent=raw,
        target_sum_exponent=target,
        required_operator_saving_exponent=saving,
        required_ttstar_saving_exponent=2 * saving,
        fixed_coefficient_operator_gate_is_sufficient=True,
        uniform_unit_ball_operator_gate_is_equivalent=True,
    )


def coupled_ttstar_determinant_split_sides(
    *,
    rows: tuple[CoupledOperatorRow, ...],
    columns: tuple[str, ...],
    operator_entries: dict[tuple[str, str], Fraction],
    row_coefficients: dict[str, Fraction],
) -> CoupledTTStarDeterminantSplit:
    """Expand one global ``TT*`` and split determinant zero/nonzero exactly.

    The split is made only after all row parameters have entered the same
    operator.  No estimate is asserted: the determinant-zero part still
    has to recombine with the resonant master term, and a spectral large
    sieve is relevant only to the determinant-nonzero part.
    """

    if not rows or not columns:
        raise ValueError("the coupled operator must have rows and columns")
    if any(
        row.short_slope_k <= 0
        or row.short_slope_l <= 0
        or gcd(row.short_slope_k, row.short_slope_l) != 1
        for row in rows
    ):
        raise ValueError("every affine slope must be a positive primitive pair")
    row_labels = tuple(row.label for row in rows)
    if len(set(row_labels)) != len(row_labels):
        raise ValueError("coupled operator row labels must be unique")
    if len(set(columns)) != len(columns):
        raise ValueError("coupled operator column labels must be unique")
    if set(row_coefficients) != set(row_labels):
        raise ValueError("row coefficient support must equal the row labels")
    if any(
        row_label not in row_coefficients or column not in columns
        for row_label, column in operator_entries
    ):
        raise ValueError("operator entry lies outside the declared supports")

    coefficients = {
        label: Fraction(row_coefficients[label]) for label in row_labels
    }
    entries = {
        (label, column): Fraction(operator_entries.get((label, column), 0))
        for label in row_labels
        for column in columns
    }
    direct = sum(
        (
            sum(
                (
                    coefficients[label] * entries[(label, column)]
                    for label in row_labels
                ),
                Fraction(0),
            )
            ** 2
            for column in columns
        ),
        Fraction(0),
    )

    gram: dict[tuple[str, str], Fraction] = {}
    zero_pairs: list[tuple[str, str]] = []
    nonzero_pairs: list[tuple[str, str]] = []
    zero_quadratic = Fraction(0)
    nonzero_quadratic = Fraction(0)
    for left in rows:
        for right in rows:
            pair = (left.label, right.label)
            gram[pair] = sum(
                (
                    entries[(left.label, column)]
                    * entries[(right.label, column)]
                    for column in columns
                ),
                Fraction(0),
            )
            contribution = (
                coefficients[left.label]
                * coefficients[right.label]
                * gram[pair]
            )
            determinant = (
                left.short_slope_k * right.short_slope_l
                - right.short_slope_k * left.short_slope_l
            )
            if determinant == 0:
                zero_pairs.append(pair)
                zero_quadratic += contribution
            else:
                nonzero_pairs.append(pair)
                nonzero_quadratic += contribution

    gram_quadratic = zero_quadratic + nonzero_quadratic
    return CoupledTTStarDeterminantSplit(
        direct_quadratic=direct,
        gram_quadratic=gram_quadratic,
        determinant_zero_quadratic=zero_quadratic,
        determinant_nonzero_quadratic=nonzero_quadratic,
        determinant_zero_pairs=tuple(zero_pairs),
        determinant_nonzero_pairs=tuple(nonzero_pairs),
        gram_entries=tuple(
            (left.label, right.label, gram[(left.label, right.label)])
            for left in rows
            for right in rows
        ),
    )


def zeta_mollifier_pairing_sides(
    *,
    mollifier_weights: tuple[tuple[int, Fraction], ...],
    zeta_indices: tuple[int, ...],
    completely_multiplicative_weight: Callable[[int], Fraction],
    shift_weights: dict[int, Fraction],
) -> tuple[Fraction, Fraction]:
    """Compare the four-variable packet with its two product coefficients.

    The callback is required to be completely multiplicative on the finite
    inputs.  The paired coefficient at ``x`` is computed independently as
    ``chi(x) * sum_{d|x, x/d in M} a_d / chi(d)``.
    """
    if any(value <= 0 for value, _ in mollifier_weights):
        raise ValueError("mollifier indices must be positive")
    if any(value <= 0 for value in zeta_indices):
        raise ValueError("zeta indices must be positive")

    direct = Fraction(0)
    for d, d_weight in mollifier_weights:
        for e, e_weight in mollifier_weights:
            for m in zeta_indices:
                for n in zeta_indices:
                    direct += (
                        d_weight
                        * e_weight
                        * completely_multiplicative_weight(m)
                        * completely_multiplicative_weight(n)
                        * shift_weights.get(m * e - n * d, Fraction(0))
                    )

    products = {
        divisor * zeta_index
        for divisor, _ in mollifier_weights
        for zeta_index in zeta_indices
    }
    product_coefficients: dict[int, Fraction] = {}
    zeta_support = set(zeta_indices)
    for product in products:
        coefficient = Fraction(0)
        for divisor, divisor_weight in mollifier_weights:
            divisor_twist = Fraction(completely_multiplicative_weight(divisor))
            if divisor_twist == 0:
                raise ValueError("multiplicative weights must be nonzero")
            if product % divisor == 0 and product // divisor in zeta_support:
                coefficient += divisor_weight / divisor_twist
        product_coefficients[product] = (
            Fraction(completely_multiplicative_weight(product)) * coefficient
        )

    paired = sum(
        (
            left_weight
            * right_weight
            * shift_weights.get(left - right, Fraction(0))
            for left, left_weight in product_coefficients.items()
            for right, right_weight in product_coefficients.items()
        ),
        Fraction(0),
    )
    return direct, paired


def common_mellin_product_constraint_sides(
    *,
    mollifier_weights: tuple[tuple[int, Fraction], ...],
    zeta_weights: tuple[tuple[int, Fraction], ...],
    completely_multiplicative_weight: Callable[[int], Fraction],
    mellin_mode_weights: tuple[tuple[int, Fraction], ...],
    product_pair_weights: dict[tuple[int, int], Fraction] | None = None,
) -> tuple[Fraction, Fraction]:
    """Recombine one common Mellin mode through both product variables.

    For a mode ``k``, put

    ``B_k(x)=sum_(d*n=x) a_d z_n chi(d)^k``.

    Complete multiplicativity makes

    ``B_k(x) B_k(y) chi(x*y)^(-k)``

    depend on the original zeta variables only through ``chi(n*m)^(-k)``.
    Thus one common Mellin parameter reconstructs the zeta-index product;
    it is not two independent orthogonality variables for the divisors.
    An optional arbitrary pair weight on ``(x, y)`` is retained verbatim.
    """

    if any(index < 1 for index, _ in mollifier_weights):
        raise ValueError("mollifier indices must be positive")
    if any(index < 1 for index, _ in zeta_weights):
        raise ValueError("zeta indices must be positive")

    def pair_weight(left_product: int, right_product: int) -> Fraction:
        if product_pair_weights is None:
            return Fraction(1)
        return product_pair_weights.get(
            (left_product, right_product), Fraction(0)
        )

    direct = Fraction(0)
    for divisor, divisor_weight in mollifier_weights:
        for other_divisor, other_divisor_weight in mollifier_weights:
            for zeta_index, zeta_weight in zeta_weights:
                for other_zeta_index, other_zeta_weight in zeta_weights:
                    zeta_product_weight = Fraction(
                        completely_multiplicative_weight(
                            zeta_index * other_zeta_index
                        )
                    )
                    if zeta_product_weight == 0:
                        raise ValueError(
                            "multiplicative weights must be nonzero"
                        )
                    for mode, mode_weight in mellin_mode_weights:
                        direct += (
                            divisor_weight
                            * other_divisor_weight
                            * zeta_weight
                            * other_zeta_weight
                            * mode_weight
                            * zeta_product_weight ** (-mode)
                            * pair_weight(
                                divisor * zeta_index,
                                other_divisor * other_zeta_index,
                            )
                        )

    paired = Fraction(0)
    for mode, mode_weight in mellin_mode_weights:
        product_coefficients: dict[int, Fraction] = {}
        for divisor, divisor_weight in mollifier_weights:
            divisor_twist = Fraction(
                completely_multiplicative_weight(divisor)
            )
            if divisor_twist == 0:
                raise ValueError("multiplicative weights must be nonzero")
            for zeta_index, zeta_weight in zeta_weights:
                product = divisor * zeta_index
                product_coefficients[product] = (
                    product_coefficients.get(product, Fraction(0))
                    + divisor_weight
                    * zeta_weight
                    * divisor_twist**mode
                )
        for left_product, left_weight in product_coefficients.items():
            for right_product, right_weight in product_coefficients.items():
                product_twist = Fraction(
                    completely_multiplicative_weight(
                        left_product * right_product
                    )
                )
                if product_twist == 0:
                    raise ValueError(
                        "multiplicative weights must be nonzero"
                    )
                paired += (
                    mode_weight
                    * left_weight
                    * right_weight
                    * product_twist ** (-mode)
                    * pair_weight(left_product, right_product)
                )
    return direct, paired


def centered_selberg_product_boundary_sides(
    *,
    mollifier_weights: tuple[tuple[int, Fraction], ...],
    product_cutoff: int,
    completely_multiplicative_weight: Callable[[int], Fraction],
    density: Fraction,
) -> tuple[Fraction, Fraction, Fraction]:
    """Center a finite zeta--mollifier convolution with every boundary kept.

    Put B(n)=sum_(d|n) a_d on n<=X.  Complete multiplicativity gives

    sum_(n<=X) (B(n)-beta) chi(n)
      = (sum_d a_d chi(d)-beta) sum_(m<=X) chi(m) - boundary,

    where boundary is the moving product tail

    sum_d a_d chi(d) sum_(X/d < m <= X) chi(m).

    At the pole density beta=sum_d a_d chi(d), the separated bulk
    vanishes but the whole centered finite sum is the negative boundary.
    This catches the invalid step of treating density centering as deletion
    of the reflected AFE/product edge.
    """

    if product_cutoff < 1:
        raise ValueError("the product cutoff must be positive")
    if any(index < 1 for index, _ in mollifier_weights):
        raise ValueError("mollifier indices must be positive")

    weights: dict[int, Fraction] = {}
    for index, weight in mollifier_weights:
        weights[index] = weights.get(index, Fraction(0)) + weight
    weights = {
        index: weight for index, weight in weights.items() if weight != 0
    }
    product_coefficients = {
        product: sum(
            (
                weight
                for divisor, weight in weights.items()
                if product % divisor == 0
            ),
            Fraction(0),
        )
        for product in range(1, product_cutoff + 1)
    }
    direct = sum(
        (
            (product_coefficients[product] - density)
            * completely_multiplicative_weight(product)
            for product in range(1, product_cutoff + 1)
        ),
        Fraction(0),
    )

    zeta_prefix = sum(
        (
            completely_multiplicative_weight(index)
            for index in range(1, product_cutoff + 1)
        ),
        Fraction(0),
    )
    mollifier_transform = sum(
        (
            weight * completely_multiplicative_weight(divisor)
            for divisor, weight in weights.items()
        ),
        Fraction(0),
    )
    boundary = sum(
        (
            weight
            * completely_multiplicative_weight(divisor)
            * sum(
                (
                    completely_multiplicative_weight(cofactor)
                    for cofactor in range(
                        product_cutoff // divisor + 1,
                        product_cutoff + 1,
                    )
                ),
                Fraction(0),
            )
            for divisor, weight in weights.items()
        ),
        Fraction(0),
    )
    recombined = (
        (mollifier_transform - density) * zeta_prefix - boundary
    )
    return direct, recombined, boundary


def q_restricted_twisted_log_signature(
    n: int,
    q: int,
    prime_twists: dict[int, Fraction],
) -> TwistedRestrictedMobiusLogSignature:
    """Exact formal signature of the q-restricted ``d^z`` divisor sum."""
    if n <= 0 or q <= 0:
        raise ValueError("twisted restricted divisor inputs must be positive")
    free_primes = _distinct_prime_factors(q_free_part(n, q))
    missing = tuple(prime for prime in free_primes if prime not in prime_twists)
    if missing:
        raise ValueError(f"missing formal prime twists: {missing}")

    restricted = tuple(d for d in divisors(n) if gcd(d, q) == 1)
    mass = Fraction(0)
    coefficient_by_prime = {prime: Fraction(0) for prime in free_primes}
    for divisor in restricted:
        twisted_weight = Fraction(1)
        valuations: dict[int, int] = {}
        for prime in free_primes:
            valuation = 0
            remainder = divisor
            while remainder % prime == 0:
                valuation += 1
                remainder //= prime
            valuations[prime] = valuation
            twisted_weight *= prime_twists[prime] ** valuation
        signed_weight = mobius(divisor) * twisted_weight
        mass += signed_weight
        for prime, valuation in valuations.items():
            coefficient_by_prime[prime] -= signed_weight * valuation

    coefficients = tuple(
        (prime, coefficient_by_prime[prime]) for prime in free_primes
    )
    return TwistedRestrictedMobiusLogSignature(
        twisted_mobius_mass=mass,
        negative_log_prime_coefficients=coefficients,
    )


def coprime_divisor_pair_identity(
    n_left: int,
    n_right: int,
    *,
    q: int,
    cutoff: int,
    left_weight: Callable[[int], Fraction],
    right_weight: Callable[[int], Fraction],
) -> CoprimeDivisorPairIdentity:
    """Verify the common-divisor inversion in the product lift.

    Each one-sided divisor already carries its Möbius coefficient.  The
    identity inserts ``sum_(c|d_left,d_right) mu(c)`` and retains the
    q-coprimality and cutoff exactly.
    """
    if n_left <= 0 or n_right <= 0 or q <= 0 or cutoff <= 0:
        raise ValueError("coprime divisor-pair inputs must be positive")

    left_divisors = tuple(
        d for d in divisors(n_left)
        if d <= cutoff and gcd(d, q) == 1
    )
    right_divisors = tuple(
        d for d in divisors(n_right)
        if d <= cutoff and gcd(d, q) == 1
    )
    left_coefficients = {
        d: Fraction(mobius(d)) * Fraction(left_weight(d))
        for d in left_divisors
    }
    right_coefficients = {
        d: Fraction(mobius(d)) * Fraction(right_weight(d))
        for d in right_divisors
    }

    direct = sum(
        (
            left_coefficients[d_left]
            * right_coefficients[d_right]
        )
        for d_left in left_divisors
        for d_right in right_divisors
        if gcd(d_left, d_right) == 1
    )

    active: list[int] = []
    inverted = Fraction(0)
    for common_divisor in divisors(gcd(n_left, n_right)):
        if mobius(common_divisor) == 0:
            continue
        left_sum = sum(
            coefficient
            for divisor, coefficient in left_coefficients.items()
            if divisor % common_divisor == 0
        )
        right_sum = sum(
            coefficient
            for divisor, coefficient in right_coefficients.items()
            if divisor % common_divisor == 0
        )
        if left_sum == 0 or right_sum == 0:
            continue
        active.append(common_divisor)
        inverted += mobius(common_divisor) * left_sum * right_sum

    return CoprimeDivisorPairIdentity(
        direct_coprime_sum=direct,
        mobius_inverted_sum=inverted,
        active_common_divisors=tuple(active),
    )


def product_lift_coefficients(
    multiplicand_coefficients: dict[int, Fraction],
    reduced_coefficients: dict[int, Fraction],
) -> dict[int, Fraction]:
    """Lift a bilinear ``m*x`` family to exact product coefficients."""
    lifted: dict[int, Fraction] = {}
    for multiplicand, multiplicand_weight in multiplicand_coefficients.items():
        if multiplicand <= 0:
            raise ValueError("product-lift multiplicands must be positive")
        for reduced, reduced_weight in reduced_coefficients.items():
            if reduced <= 0:
                raise ValueError("product-lift reduced variables must be positive")
            product = multiplicand * reduced
            lifted[product] = lifted.get(product, Fraction(0)) + (
                multiplicand_weight * reduced_weight
            )
    return lifted


def product_lift_shifted_correlation(
    left: dict[int, Fraction],
    right: dict[int, Fraction],
    shift: int,
) -> Fraction:
    """Return ``sum_n left(n) right(n-shift)`` with finite support."""
    return sum(
        (
            left_weight * right.get(product - shift, Fraction(0))
            for product, left_weight in left.items()
        ),
        start=Fraction(0),
    )


def c_u(a: int, cutoff_u: int) -> int:
    return sum(mobius(d) for d in divisors(a) if d <= cutoff_u)


def full_truncated_mobius_convolution(
    *,
    n: int,
    cutoff_u: int,
) -> int:
    """Evaluate ``(mu*c_U)(n)=mu(n) 1_(n<=U)`` as a finite sum."""
    if n < 1 or cutoff_u < 1:
        raise ValueError("require n, cutoff_u >= 1")
    return sum(
        mobius(s) * c_u(n // s, cutoff_u)
        for s in divisors(n)
    )


def restricted_truncated_mobius_convolution(
    *,
    n: int,
    cutoff_u: int,
) -> int:
    """Evaluate the actual ``a>U`` convolution in one Type sector."""
    if n < 1 or cutoff_u < 1:
        raise ValueError("require n, cutoff_u >= 1")
    return sum(
        mobius(s) * c_u(n // s, cutoff_u)
        for s in divisors(n)
        if n // s > cutoff_u
    )


def mobius_unsigned_sector_recombination(
    *,
    n: int,
    cutoff_u: int,
) -> MobiusUnsignedSectorRecombination:
    """Group the exact Type identity by its signed outer product.

    For ``n>U``, expand

    ``mu(n)=-sum_(d*e*y=n, d*e>U, d<=U) mu(d)mu(y)``.

    BBLR can place ``d*y`` in an arbitrary outer coefficient and the
    unsigned quotient ``e`` in an inner slot.  The outer-product-one
    sector is uniquely ``d=y=1`` and therefore contributes ``-1`` for
    every ``n>U``.  Its cancellation is visible only after all nontrivial
    outer products have been recombined.
    """
    if n <= cutoff_u or cutoff_u < 1:
        raise ValueError("require n>cutoff_u>=1")

    contributions: dict[int, int] = {}
    for d in divisors(n):
        if d > cutoff_u or mobius(d) == 0:
            continue
        quotient = n // d
        for y in divisors(quotient):
            coefficient = -mobius(d) * mobius(y)
            if coefficient == 0:
                continue
            e = quotient // y
            if d * e <= cutoff_u:
                continue
            outer_product = d * y
            contributions[outer_product] = (
                contributions.get(outer_product, 0) + coefficient
            )

    pure = contributions.get(1, 0)
    recombined = sum(contributions.values())
    expected = mobius(n)
    return MobiusUnsignedSectorRecombination(
        n=n,
        cutoff_u=cutoff_u,
        mobius_value=expected,
        pure_unsigned_outer_product=1,
        pure_unsigned_contribution=pure,
        nontrivial_signed_contribution=recombined - pure,
        recombined_contribution=recombined,
        outer_contributions=tuple(sorted(contributions.items())),
        recombination_identity_verified=(pure == -1 and recombined == expected),
    )


def four_mobius_unsigned_sector_recombination(
    *,
    values: tuple[int, int, int, int],
    cutoff_u: int,
) -> FourMobiusUnsignedSectorRecombination:
    """Identify the all-unsigned cell in four simultaneous Type identities."""
    if len(values) != 4:
        raise ValueError("require exactly four Möbius variables")
    one_variable = tuple(
        mobius_unsigned_sector_recombination(n=n, cutoff_u=cutoff_u)
        for n in values
    )
    recombined_product = 1
    pure_product = 1
    for audit in one_variable:
        recombined_product *= audit.recombined_contribution
        pure_product *= audit.pure_unsigned_contribution
    verified = all(audit.recombination_identity_verified for audit in one_variable)
    return FourMobiusUnsignedSectorRecombination(
        values=values,
        cutoff_u=cutoff_u,
        recombined_mobius_product=recombined_product,
        pure_unsigned_bblr_box_contribution=pure_product,
        all_other_boxes_contribution=recombined_product - pure_product,
        pure_box_is_unweighted_and_positive=(pure_product == 1),
        recombination_identity_verified=verified,
    )


def restricted_zero_ray_pair_convolution(
    *,
    u: int,
    v: int,
    k: int,
    cutoff_u: int,
) -> RestrictedZeroRayPairConvolution:
    """Evaluate both restricted convolutions on one primitive zero ray.

    On squarefree support, ``(u,v)=1`` and the two products ``u*k`` and
    ``v*k`` squarefree imply ``(k,u*v)=1``.  Hence the common factor
    contributes ``mu(k)^2=1`` and the paired main coefficient is exactly
    ``mu(u)*mu(v)`` rather than a Möbius weight in ``k``.
    """
    if u < 1 or v < 1 or k < 1 or cutoff_u < 1:
        raise ValueError("require u, v, k, cutoff_u >= 1")
    if gcd(u, v) != 1:
        raise ValueError("require primitive coprime ray coordinates")

    left_product = u * k
    right_product = v * k
    left_sector_sum = restricted_truncated_mobius_convolution(
        n=left_product,
        cutoff_u=cutoff_u,
    )
    right_sector_sum = restricted_truncated_mobius_convolution(
        n=right_product,
        cutoff_u=cutoff_u,
    )
    pair_sector_product = left_sector_sum * right_sector_sum
    squarefree_ray_support = (
        mobius(left_product) != 0 and mobius(right_product) != 0
    )
    common_k_mobius_cancels_exactly = (
        left_product > cutoff_u
        and right_product > cutoff_u
        and squarefree_ray_support
        and pair_sector_product == mobius(u) * mobius(v)
    )

    return RestrictedZeroRayPairConvolution(
        u=u,
        v=v,
        k=k,
        cutoff_u=cutoff_u,
        left_product=left_product,
        right_product=right_product,
        left_sector_sum=left_sector_sum,
        right_sector_sum=right_sector_sum,
        pair_sector_product=pair_sector_product,
        squarefree_ray_support=squarefree_ray_support,
        common_k_mobius_cancels_exactly=(
            common_k_mobius_cancels_exactly
        ),
    )


def _normalized_modular_phase(
    *,
    numerator: int,
    invert: int,
    modulus: int,
) -> Fraction:
    if modulus < 1:
        raise ValueError("modulus must be positive")
    if modulus == 1:
        return Fraction(0)
    if gcd(invert, modulus) != 1:
        raise ValueError("phase denominator is not invertible")
    residue = numerator * pow(invert, -1, modulus) % modulus
    return Fraction(residue, modulus)


def _fractional_part(value: Fraction) -> Fraction:
    return Fraction(value.numerator % value.denominator, value.denominator)


def common_b_phase_reciprocity(
    *,
    n1: int,
    y1: int,
    n2: int,
    y2: int,
    b: int,
) -> CommonBPhaseReciprocity:
    """Rewrite the full common-``b`` phase without imposing ``b|Delta``.

    With ``Delta=n1*y2-n2*y1`` and ``(b,y1*y2)=1``, the phase is

    ``Delta*bar(y1*y2)/b``
    `` = Delta/(b*y1*y2)-Delta*bar(b)/(y1*y2) (mod 1)``.

    Divisibility by ``b`` is only a special zero mode, not a condition in
    the original expanded square.
    """
    if min(y1, y2, b) < 1:
        raise ValueError("require positive y1, y2, b")
    product = y1 * y2
    if gcd(b, product) != 1:
        raise ValueError("require b coprime to y1*y2")

    determinant = n1 * y2 - n2 * y1
    original_phase = _fractional_part(
        _normalized_modular_phase(
            numerator=n1,
            invert=y1,
            modulus=b,
        )
        + _normalized_modular_phase(
            numerator=-n2,
            invert=y2,
            modulus=b,
        )
    )
    determinant_phase = _normalized_modular_phase(
        numerator=determinant,
        invert=product,
        modulus=b,
    )
    smooth_real_phase = Fraction(determinant, b * product)
    dual_reciprocal_phase = _normalized_modular_phase(
        numerator=-determinant,
        invert=b,
        modulus=product,
    )
    reciprocal_completed_phase = _fractional_part(
        smooth_real_phase + dual_reciprocal_phase
    )

    return CommonBPhaseReciprocity(
        determinant=determinant,
        original_phase=original_phase,
        determinant_phase=determinant_phase,
        smooth_real_phase=smooth_real_phase,
        dual_reciprocal_phase=dual_reciprocal_phase,
        reciprocal_completed_phase=reciprocal_completed_phase,
        b_divides_determinant=determinant % b == 0,
    )


def lcm_b_phase_compression(
    *,
    n1: int,
    a1: int,
    s1: int,
    n2: int,
    a2: int,
    s2: int,
    b: int,
) -> LcmBPhaseCompression:
    """Compress the squared Type-II phase to lcm(s1,s2).

    This checks the original two reciprocal phases against the single
    common-b phase with numerator
    C=-n1*bar(a1)*(lcm/s1)+n2*bar(a2)*(lcm/s2).
    """
    if min(a1, s1, a2, s2, b) < 1:
        raise ValueError("require positive factors and moduli")
    if gcd(a1 * b, s1) != 1 or gcd(a2 * b, s2) != 1:
        raise ValueError("require a_i*b invertible modulo s_i")

    lcm_modulus = s1 * s2 // gcd(s1, s2)
    original_phase = _fractional_part(
        _normalized_modular_phase(
            numerator=-n1,
            invert=a1 * b,
            modulus=s1,
        )
        + _normalized_modular_phase(
            numerator=n2,
            invert=a2 * b,
            modulus=s2,
        )
    )
    compressed_numerator = (
        -n1 * pow(a1, -1, s1) * (lcm_modulus // s1)
        + n2 * pow(a2, -1, s2) * (lcm_modulus // s2)
    )
    compressed_phase = _fractional_part(
        _normalized_modular_phase(
            numerator=compressed_numerator,
            invert=b,
            modulus=lcm_modulus,
        )
    )
    if original_phase != compressed_phase:
        raise AssertionError("lcm phase compression failed")

    return LcmBPhaseCompression(
        lcm_modulus=lcm_modulus,
        compressed_numerator=compressed_numerator % lcm_modulus,
        original_phase=original_phase,
        compressed_phase=compressed_phase,
    )


def zero_ray_phase_reduction(
    *,
    u: int,
    k: int,
    s: int,
    a: int,
    b: int,
    g: int,
) -> ZeroRayPhaseReduction:
    """Remove the primitive slope from all zero-ray reciprocal phases.

    Assume the original squarefree support, ``s*a=u*k`` and
    ``(u,k)=(s,a)=(u*k,b)=1``.  Splitting the prime allocation as
    ``s=s_u*s_k`` and ``a=a_u*a_k`` gives

    ``g*u*bar(s*b)/a = g*bar(s_k*b)/a_k (mod 1)``.

    The smooth real phase is exactly ``-g/(k*b)``, and the common-``b``
    phase is ``g*bar(k)/b``.  Thus none of these phases has a primitive
    slope conductor.
    """
    if min(u, k, s, a, b) < 1 or g == 0:
        raise ValueError("require positive factors and nonzero g")
    if mobius(u * k) == 0:
        raise ValueError("require squarefree u*k")
    if gcd(u, k) != 1 or s * a != u * k:
        raise ValueError("require coprime u,k and s*a=u*k")
    if gcd(s, a) != 1 or gcd(u * k, b) != 1:
        raise ValueError("require the original coprimality support")

    s_u = gcd(s, u)
    a_u = gcd(a, u)
    s_k = gcd(s, k)
    a_k = gcd(a, k)
    if s_u * a_u != u or s_k * a_k != k:
        raise AssertionError("squarefree prime allocation failed")
    if s_u * s_k != s or a_u * a_k != a:
        raise AssertionError("factorization allocation mismatch")

    original_fixed_phase = _normalized_modular_phase(
        numerator=g * u,
        invert=s * b,
        modulus=a,
    )
    reduced_fixed_phase = _normalized_modular_phase(
        numerator=g,
        invert=s_k * b,
        modulus=a_k,
    )
    original_real_phase = Fraction(-g * u, a * b * s)
    product_real_phase = Fraction(-g, k * b)
    original_common_b_phase = _normalized_modular_phase(
        numerator=g * u,
        invert=s * a,
        modulus=b,
    )
    product_common_b_phase = _normalized_modular_phase(
        numerator=g,
        invert=k,
        modulus=b,
    )
    primitive_slope_removed = (
        original_fixed_phase == reduced_fixed_phase
        and original_real_phase == product_real_phase
        and original_common_b_phase == product_common_b_phase
    )

    return ZeroRayPhaseReduction(
        s_u=s_u,
        a_u=a_u,
        s_k=s_k,
        a_k=a_k,
        original_fixed_phase=original_fixed_phase,
        reduced_fixed_phase=reduced_fixed_phase,
        original_real_phase=original_real_phase,
        product_real_phase=product_real_phase,
        original_common_b_phase=original_common_b_phase,
        product_common_b_phase=product_common_b_phase,
        primitive_slope_removed_from_reciprocal_phase=(
            primitive_slope_removed
        ),
    )


def split_mobius_identity(
    n: int,
    *,
    cutoff_u: int,
    cutoff_v: int,
) -> tuple[int, int, int]:
    """Return ``mu(n)``, the Type-I sum, and the Type-II sum.

    This interface requires ``n > cutoff_u``.  The identity checked is
    ``mu(n) = -(type_i + type_ii)``.
    """
    if n <= cutoff_u:
        raise ValueError("identity requires n > cutoff_u")
    type_i = 0
    type_ii = 0
    for a in divisors(n):
        if a <= cutoff_u:
            continue
        b = n // a
        term = c_u(a, cutoff_u) * mobius(b)
        if b <= cutoff_v:
            type_i += term
        else:
            type_ii += term
    return mobius(n), type_i, type_ii


def double_split_mobius_identity(
    r: int,
    s: int,
    *,
    cutoff_u: int,
    cutoff_v: int,
) -> tuple[int, dict[str, int]]:
    """Split ``mu(r) * mu(s)`` into the four exact Type sectors.

    Each one-variable identity has a minus sign.  Their product therefore
    has a plus sign in every ``I/I``, ``I/II``, ``II/I``, and ``II/II``
    sector.
    """
    mu_r, r_i, r_ii = split_mobius_identity(
        r, cutoff_u=cutoff_u, cutoff_v=cutoff_v
    )
    mu_s, s_i, s_ii = split_mobius_identity(
        s, cutoff_u=cutoff_u, cutoff_v=cutoff_v
    )
    sectors = {
        "I/I": r_i * s_i,
        "I/II": r_i * s_ii,
        "II/I": r_ii * s_i,
        "II/II": r_ii * s_ii,
    }
    return mu_r * mu_s, sectors


def crt_reciprocity_numerators(
    *,
    s: int,
    a: int,
    b: int,
    n: int,
) -> tuple[Fraction, Fraction, Fraction]:
    """Return the three rational phases in the squarefree CRT identity.

    If ``(a,b)=(s,a*b)=1``, then modulo one

    ``n*bar(s)/(a*b) = n*bar(s*b)/a + n*bar(s*a)/b``.

    Returning exact :class:`Fraction` values lets tests check the congruence
    without floating-point evaluation of the exponential.
    """
    if a <= 1 or b <= 1 or gcd(a, b) != 1 or gcd(s, a * b) != 1:
        raise ValueError("require a,b > 1 and (a,b)=(s,a*b)=1")
    inverse = Fraction(n * pow(s, -1, a * b), a * b)
    mod_a = Fraction(n * pow(s * b, -1, a), a)
    mod_b = Fraction(n * pow(s * a, -1, b), b)
    return inverse, mod_a, mod_b


def poisson_congruence_reparametrization(
    *,
    r: int,
    s: int,
    delta: int,
    k: int,
) -> tuple[int, int]:
    """Reparametrize an ``h``-Poisson frequency by a shifted equation.

    With ``bar(r)`` chosen modulo ``s``, put
    ``v = k*s + delta*bar(r)``.  Then the returned integer ``j`` satisfies
    the exact equation ``delta = r*v - j*s``.
    """
    if r <= 0 or s <= 1 or gcd(r, s) != 1:
        raise ValueError("require r > 0, s > 1, and (r,s)=1")
    v = k * s + delta * pow(r, -1, s)
    numerator = r * v - delta
    assert numerator % s == 0
    return v, numerator // s


def determinant_lattice_solution(
    *,
    r: int,
    s: int,
    delta: int,
    translate: int,
) -> tuple[int, int]:
    """Parameterize the full affine lattice ``r*v-j*s=delta``.

    Choose ``v_0`` as the inverse of ``r`` modulo ``s`` and put
    ``j_0=(r*v_0-1)/s``.  Every translated pair

    ``j=delta*j_0+translate*r``,
    ``v=delta*v_0+translate*s``

    has determinant ``delta``; conversely every integral solution is one
    such translate because ``(r,s)=1``.
    """
    if r <= 0 or s <= 1 or gcd(r, s) != 1:
        raise ValueError("require r > 0, s > 1, and (r,s)=1")
    v_0 = pow(r, -1, s)
    j_0 = (r * v_0 - 1) // s
    return delta * j_0 + translate * r, delta * v_0 + translate * s


def _extended_gcd_nonnegative(a: int, b: int) -> tuple[int, int, int]:
    if a < 0 or b < 0:
        raise ValueError("extended gcd inputs must be nonnegative")
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t
    return old_r, old_s, old_t


def determinant_line_coordinates(
    *,
    j: int,
    v: int,
    delta: int,
) -> DeterminantLineCoordinates:
    """Parameterize exactly ``r*v-j*s=delta`` by one integer ``n``.

    Put ``g=(|j|,|v|)``.  Solubility forces ``g|delta``.  After dividing
    by ``g``, Bezout gives a particular solution; the primitive kernel
    vector is ``(j/g,v/g)``.  Hence every solution is returned exactly
    once by :meth:`DeterminantLineCoordinates.solution`.
    """
    if j == 0 or v == 0 or delta == 0:
        raise ValueError("require nonzero j, v, and delta")
    common_gcd = gcd(abs(j), abs(v))
    if delta % common_gcd != 0:
        raise ValueError("determinant shift is not divisible by (j,v)")

    primitive_j = j // common_gcd
    primitive_v = v // common_gcd
    shift_quotient = delta // common_gcd
    bezout_gcd, x_abs, y_abs = _extended_gcd_nonnegative(
        abs(primitive_v),
        abs(primitive_j),
    )
    if bezout_gcd != 1:
        raise AssertionError("primitive determinant slopes are not coprime")
    x = x_abs if primitive_v > 0 else -x_abs
    y = y_abs if primitive_j > 0 else -y_abs
    if x * primitive_v + y * primitive_j != 1:
        raise AssertionError("signed Bezout normalization failed")

    particular_r = shift_quotient * x
    particular_s = -shift_quotient * y
    if (
        particular_r * primitive_v
        - particular_s * primitive_j
        != shift_quotient
    ):
        raise AssertionError("particular determinant solution failed")

    return DeterminantLineCoordinates(
        gcd_j_v=common_gcd,
        primitive_j=primitive_j,
        primitive_v=primitive_v,
        shift_quotient=shift_quotient,
        particular_r=particular_r,
        particular_s=particular_s,
    )


def determinant_line_coprimality_residue(
    coordinates: DeterminantLineCoordinates,
    *,
    divisor: int,
) -> int:
    """Return the unique ``n mod divisor`` making both line entries zero."""
    if divisor < 1 or abs(coordinates.shift_quotient) % divisor != 0:
        raise ValueError("require a positive divisor of the shift quotient")
    if mobius(divisor) == 0:
        raise ValueError("require a squarefree divisor")
    hits = tuple(
        n
        for n in range(divisor)
        if all(value % divisor == 0 for value in coordinates.solution(n))
    )
    if len(hits) != 1:
        raise AssertionError("coprime primitive slopes must give one residue")
    return hits[0]


def determinant_line_coprimality_indicator(
    coordinates: DeterminantLineCoordinates,
    *,
    n: int,
) -> int:
    """Evaluate the exact divisor expansion of ``1_(r_n,s_n)=1``."""
    total = 0
    for divisor in divisors(abs(coordinates.shift_quotient)):
        coefficient = mobius(divisor)
        if coefficient == 0:
            continue
        residue = determinant_line_coprimality_residue(
            coordinates,
            divisor=divisor,
        )
        if n % divisor == residue:
            total += coefficient
    return total


def determinant_slope_square_coordinates(
    *,
    r1: int,
    s1: int,
    r2: int,
    s2: int,
    primitive_j: int,
    primitive_v: int,
) -> DeterminantSlopeSquareCoordinates:
    """Recover the common slope in the square of a determinant-line sum.

    With ``delta_i=r_i*v-s_i*j`` and
    ``Delta=r1*s2-r2*s1``, Cramer's rule gives, for ``Delta != 0``,

    ``v=(delta1*s2-delta2*s1)/Delta`` and
    ``j=(delta1*r2-delta2*r1)/Delta``.

    If ``Delta=0`` and both positive pairs ``(r_i,s_i)`` are primitive,
    proportionality forces the pairs to be identical.  This is exactly
    the positive identity diagonal in the slope square function.
    """
    if min(r1, s1, r2, s2) < 1:
        raise ValueError("require positive determinant-row entries")
    if gcd(r1, s1) != 1 or gcd(r2, s2) != 1:
        raise ValueError("require primitive determinant-row pairs")
    if primitive_j == 0 or primitive_v == 0:
        raise ValueError("require a nonzero primitive slope")
    if gcd(abs(primitive_j), abs(primitive_v)) != 1:
        raise ValueError("require coprime primitive slope entries")

    shift1 = r1 * primitive_v - s1 * primitive_j
    shift2 = r2 * primitive_v - s2 * primitive_j
    cross_determinant = r1 * s2 - r2 * s1
    if cross_determinant == 0:
        if (r1, s1) != (r2, s2):
            raise AssertionError(
                "positive primitive proportional pairs must be equal"
            )
        return DeterminantSlopeSquareCoordinates(
            shift1=shift1,
            shift2=shift2,
            cross_determinant=0,
            recovered_primitive_j=None,
            recovered_primitive_v=None,
            zero_determinant_is_identity_diagonal=True,
        )

    v_numerator = shift1 * s2 - shift2 * s1
    j_numerator = shift1 * r2 - shift2 * r1
    if (
        v_numerator % cross_determinant != 0
        or j_numerator % cross_determinant != 0
    ):
        raise AssertionError("Cramer numerators are not integral")
    recovered_v = v_numerator // cross_determinant
    recovered_j = j_numerator // cross_determinant
    if (recovered_j, recovered_v) != (primitive_j, primitive_v):
        raise AssertionError("Cramer recovery changed the primitive slope")

    return DeterminantSlopeSquareCoordinates(
        shift1=shift1,
        shift2=shift2,
        cross_determinant=cross_determinant,
        recovered_primitive_j=recovered_j,
        recovered_primitive_v=recovered_v,
        zero_determinant_is_identity_diagonal=False,
    )


def determinant_cokernel_coordinates(
    *,
    r1: int,
    s1: int,
    r2: int,
    s2: int,
) -> DeterminantCokernelCoordinates:
    """Audit the finite cokernel behind the two Cramer divisibilities.

    Put

    ``B=((r1,-s1),(r2,-s2))`` and
    ``(delta1,delta2)^t = B (v,j)^t``.

    If both positive rows ``(r_i,s_i)`` are primitive and
    ``Delta=r1*s2-r2*s1`` is nonzero, the gcd of all entries of ``B`` is
    one.  The Smith invariants are therefore ``1, |Delta|``.  Hence the
    two displayed Cramer congruences have *joint* index ``|Delta|``;
    treating them as two independent modulus-``Delta`` conditions would
    introduce a false extra factor ``|Delta|``.

    The returned finite sets verify both sides of exact character
    orthogonality.  ``admissible_shift_residues`` is the image of ``B``
    modulo ``|Delta|`` (equivalently the Cramer-integral shifts), while
    ``annihilator_characters`` is its Pontryagin annihilator.  Each set
    has exactly ``|Delta|`` elements.
    """
    if min(r1, s1, r2, s2) < 1:
        raise ValueError("require positive determinant rows")
    if gcd(r1, s1) != 1 or gcd(r2, s2) != 1:
        raise ValueError("require primitive determinant rows")

    cross_determinant = r1 * s2 - r2 * s1
    if cross_determinant == 0:
        raise ValueError("require a nonzero cross determinant")
    modulus = abs(cross_determinant)
    first_invariant = gcd(gcd(r1, s1), gcd(r2, s2))
    if first_invariant != 1:
        raise AssertionError(
            "primitive rows must have first Smith invariant one"
        )
    second_invariant = modulus

    admissible: list[tuple[int, int]] = []
    annihilator: list[tuple[int, int]] = []
    for first in range(modulus):
        for second in range(modulus):
            v_numerator = first * s2 - second * s1
            j_numerator = first * r2 - second * r1
            if (
                v_numerator % modulus == 0
                and j_numerator % modulus == 0
            ):
                admissible.append((first, second))
            if (
                (first * r1 + second * r2) % modulus == 0
                and (first * s1 + second * s2) % modulus == 0
            ):
                annihilator.append((first, second))

    if len(admissible) != modulus or len(annihilator) != modulus:
        raise AssertionError("determinant cokernel cardinality changed")

    return DeterminantCokernelCoordinates(
        modulus=modulus,
        smith_first_invariant=first_invariant,
        smith_second_invariant=second_invariant,
        admissible_shift_residues=tuple(admissible),
        annihilator_characters=tuple(annihilator),
        cokernel_is_cyclic=True,
    )


def _ceil_div(numerator: int, denominator: int) -> int:
    return -((-numerator) // denominator)


def signed_shift_solutions(
    *,
    r: int,
    s: int,
    v: int,
    delta_min: int,
    delta_max: int,
    sign: int,
) -> tuple[tuple[int, int], ...]:
    """Return every ``(j,delta)`` in one signed determinant window.

    The returned solutions satisfy ``delta=r*v-j*s`` and
    ``delta_min <= sign*delta <= delta_max``.  If the window width is
    strictly smaller than ``s``, the tuple has length at most one.
    """
    if r <= 0 or s <= 0:
        raise ValueError("require r,s > 0")
    if delta_min < 0 or delta_min > delta_max:
        raise ValueError("require 0 <= delta_min <= delta_max")
    if sign not in (-1, 1):
        raise ValueError("sign must be -1 or 1")
    product = r * v
    if sign == 1:
        j_min = _ceil_div(product - delta_max, s)
        j_max = (product - delta_min) // s
    else:
        j_min = _ceil_div(product + delta_min, s)
        j_max = (product + delta_max) // s
    return tuple((j, product - j * s) for j in range(j_min, j_max + 1))


def nonzero_character_orthogonality(modulus: int, integer: int) -> int:
    """Exact sum of all nontrivial additive characters modulo ``modulus``.

    Algebraically,
    ``sum_{c=1}^{s-1} exp(2*pi*i*c*n/s)`` is ``s-1`` when ``s|n`` and
    ``-1`` otherwise.  Returning that integer avoids floating-point roots
    of unity in the finite-completion audit.
    """
    if modulus <= 1:
        raise ValueError("modulus must exceed one")
    return modulus - 1 if integer % modulus == 0 else -1


def centered_completion_via_orthogonality(
    values: tuple[int | Fraction, ...],
    *,
    residue: int,
) -> Fraction:
    """Evaluate the nonzero-frequency centered finite Fourier inversion.

    For a function ``G`` on ``Z/sZ``, nonzero-character orthogonality gives

    ``G(n)-G(0) = (1/s) sum_x G(x) [K(n-x)-K(-x)]``,

    where ``K(y)`` is the sum of the nontrivial additive characters.  Thus
    a signed shift weight with ``G(0)=0`` is recovered using only nonzero
    completion frequencies and the centered phase ``e(c*n/s)-1``.
    """
    modulus = len(values)
    if modulus <= 1:
        raise ValueError("values must define a group of order > 1")
    n = residue % modulus
    total = sum(
        Fraction(value)
        * (
            nonzero_character_orthogonality(modulus, n - x)
            - nonzero_character_orthogonality(modulus, -x)
        )
        for x, value in enumerate(values)
    )
    return total / modulus


def centered_product_frequency_coefficients(
    terms: tuple[tuple[int, int, int | Fraction], ...],
) -> dict[int, Fraction]:
    """Group a centered ``(c,v)`` sum exactly by ``a=c*v``.

    The centered completion has no ``c=0`` term and carries the phase
    ``e(c*v*r/s)-1``.  Terms with ``v=0`` therefore vanish identically.
    Every remaining pair has a nonzero integer product, so finite
    reindexing gives one coefficient for each product frequency ``a``.
    """
    grouped: dict[int, Fraction] = {}
    for c, v, weight in terms:
        if c == 0:
            raise ValueError("completion frequency c must be nonzero")
        if v == 0:
            continue
        product = c * v
        new_weight = grouped.get(product, Fraction(0)) + Fraction(weight)
        if new_weight:
            grouped[product] = new_weight
        else:
            grouped.pop(product, None)
    return grouped


def bilinear_gauss_via_orthogonality(
    *,
    r: int,
    modulus: int,
    c: int,
    v: int,
) -> tuple[int, int]:
    """Return the exact coefficient and phase of the finite bilinear kernel.

    If ``bar(r)`` is the inverse of ``r`` modulo ``s``, summing first in
    ``x`` gives

    ``sum_{x,y mod s} e((c*x+v*y-bar(r)*x*y)/s)``
    ``= s*e(r*c*v/s)``.

    The return value ``(s, r*c*v mod s)`` records this identity without
    evaluating any floating-point roots of unity.
    """
    if modulus <= 1 or gcd(r, modulus) != 1:
        raise ValueError("require modulus > 1 and (r,modulus)=1")
    surviving_y = (r * c) % modulus
    return modulus, (v * surviving_y) % modulus


def double_centered_completion_via_orthogonality(
    values: tuple[tuple[int | Fraction, ...], ...],
    *,
    residue_x: int,
    residue_y: int,
) -> Fraction:
    """Evaluate exact two-dimensional nonzero-character centering.

    For a function ``F`` on ``(Z/sZ)^2``, the centered transform equals

    ``F(x,y)-F(x,0)-F(0,y)+F(0,0)``.

    In particular, if ``F`` vanishes on both coordinate axes, its complete
    value is recovered using only nonzero characters in both variables.
    """
    modulus = len(values)
    if modulus <= 1 or any(len(row) != modulus for row in values):
        raise ValueError("values must be a square group table of order > 1")
    target_x = residue_x % modulus
    target_y = residue_y % modulus
    total = Fraction(0)
    for x, row in enumerate(values):
        kernel_x = (
            nonzero_character_orthogonality(modulus, target_x - x)
            - nonzero_character_orthogonality(modulus, -x)
        )
        for y, value in enumerate(row):
            kernel_y = (
                nonzero_character_orthogonality(modulus, target_y - y)
                - nonzero_character_orthogonality(modulus, -y)
            )
            total += Fraction(value) * kernel_x * kernel_y
    return total / (modulus * modulus)


def double_zero_sum_nonzero_mass(
    values: tuple[tuple[int | Fraction, ...], ...],
) -> tuple[Fraction, Fraction]:
    """Identify the constant mass left after double centering.

    If every row and every column of ``Theta`` sums to zero, then

    ``sum_(c != 0, v != 0) Theta(c,v) = Theta(0,0)``.

    Thus the ``-1`` in a centered phase does not vanish by itself; its
    nonzero-frequency contribution is exactly ``-Theta(0,0)``.  The
    equality uses the full two-dimensional zero-sum structure.
    """
    modulus = len(values)
    if modulus == 0 or any(len(row) != modulus for row in values):
        raise ValueError("values must be a nonempty square group table")
    table = tuple(tuple(Fraction(value) for value in row) for row in values)
    if any(sum(row, Fraction(0)) != 0 for row in table) or any(
        sum((table[c][v] for c in range(modulus)), Fraction(0)) != 0
        for v in range(modulus)
    ):
        raise ValueError("row and column sums must vanish")
    nonzero_mass = sum(
        (
            table[c][v]
            for c in range(1, modulus)
            for v in range(1, modulus)
        ),
        Fraction(0),
    )
    return nonzero_mass, table[0][0]


def restricted_squarefree_expansion(*, e: int, modulus: int) -> int:
    """Expand the exact squarefree and coprimality support of ``e``.

    The returned double divisor sum is

    ``sum_(k^2|e) mu(k) * sum_(ell|(e,modulus)) mu(ell)``

    and therefore equals ``mu(e)^2 * 1_(e,modulus)=1``.  This is the
    expansion required before Poisson summation can turn the remaining
    cofactor into an unweighted integer variable.
    """
    if e <= 0 or modulus <= 0:
        raise ValueError("e and modulus must be positive")
    squarefree_sum = sum(
        mobius(k) for k in divisors(e) if e % (k * k) == 0
    )
    coprimality_sum = sum(mobius(ell) for ell in divisors(gcd(e, modulus)))
    return squarefree_sum * coprimality_sum


def long_cutoff_quotient_progression(
    *,
    j: int,
    delta: int,
    b: int,
    d: int,
    v: int,
) -> tuple[int, int] | None:
    """Reduce the exact integrality condition for the quotient cofactor.

    After writing ``r=a*b`` and expanding
    ``c_U(a)=sum_(d|a,d<=U) mu(d)`` with ``a=d*e``, the determinant

    ``d*e*b*v-j*s=delta``

    makes ``e`` integral precisely when ``j*s+delta`` is divisible by
    ``b*d*v``.  Put ``M=|b*d*v|`` and ``g=(j,M)``.  There is no solution
    unless ``g|delta``; otherwise the condition is the single reduced
    progression

    ``s = -(delta/g)*(j/g)^(-1) (mod M/g)``.

    The returned residue is the least nonnegative representative.  In
    particular the gcd reduction can only decrease the modulus used by a
    possible arithmetic-progression theorem.
    """
    if b <= 0 or d <= 0 or v == 0:
        raise ValueError("b,d must be positive and v nonzero")
    modulus = abs(b * d * v)
    common = gcd(j, modulus)
    if delta % common:
        return None
    reduced_modulus = modulus // common
    if reduced_modulus == 1:
        return 1, 0
    reduced_j = j // common
    reduced_delta = delta // common
    residue = (-reduced_delta * pow(reduced_j, -1, reduced_modulus)) % (
        reduced_modulus
    )
    return reduced_modulus, residue


@dataclass(frozen=True)
class TypeScaleBounds:
    u_exp: Fraction
    v_exp: Fraction
    type_i_a_min: Fraction
    type_ii_a_min: Fraction
    type_ii_a_max: Fraction
    type_ii_b_min: Fraction
    type_ii_b_max: Fraction


def type_scale_bounds(
    rho: Fraction,
    *,
    u: Fraction,
    v: Fraction,
) -> TypeScaleBounds:
    if rho < 0 or not (0 < u < 1) or not (0 < v < 1):
        raise ValueError("require rho >= 0 and 0 < u,v < 1")
    u_exp = rho * u
    v_exp = rho * v
    return TypeScaleBounds(
        u_exp=u_exp,
        v_exp=v_exp,
        type_i_a_min=rho - v_exp,
        type_ii_a_min=u_exp,
        type_ii_a_max=rho - v_exp,
        type_ii_b_min=v_exp,
        type_ii_b_max=rho - u_exp,
    )
