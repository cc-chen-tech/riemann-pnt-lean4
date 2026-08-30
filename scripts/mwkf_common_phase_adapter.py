"""Finite common-frequency adapter; no analytic gate is asserted.

The values lie in Q[z]/(z**g - 1), before evaluation at exp(2*pi*i/g).
Input type_weights already contains its Mobius or exact Type coefficient.
The common outer scalar mu(g*p) is not included.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from math import gcd, isqrt

from scripts.mwkf_mobius_type_identity import mobius


@dataclass(frozen=True)
class CommonFrequencyProfile:
    direct_raw: dict[int, tuple[F, ...]]
    raw: dict[int, tuple[F, ...]]
    direct_centered: dict[int, tuple[F, ...]]
    centered: dict[int, tuple[F, ...]]
    retained_products: tuple[tuple[int, int], ...]


def common_frequency_profile(
    *,
    common_modulus: int,
    active_prime: int,
    phase_label: int,
    frequency: int,
    h_weights: dict[int, F],
    delta_weights: dict[int, F],
    type_weights: dict[int, F],
) -> CommonFrequencyProfile:
    """Retain both common phases and center only the active coordinate.

    All supports are literal finite supports.  Nonunits at g*p are
    discarded by zero extension; there is no enlargement of endpoints.
    A negative h or delta is allowed; a Type argument must be positive.
    """
    g, p = common_modulus, active_prime
    if g < 2 or mobius(g) == 0:
        raise ValueError("common modulus must be squarefree and at least two")
    if p < 2 or any(p % d == 0 for d in range(2, isqrt(p) + 1)):
        raise ValueError("active modulus must be prime")
    if gcd(g, p) != 1 or gcd(phase_label, g) != 1:
        raise ValueError("active prime and phase label must be common units")
    if 0 in h_weights or 0 in delta_weights:
        raise ValueError("product factors must be nonzero")
    if any(n <= 0 for n in type_weights):
        raise ValueError("Type arguments must be positive")

    products = tuple((h, delta) for h in h_weights for delta in delta_weights)
    terms = tuple(
        (h * delta, n, F(h_weights[h]) * F(delta_weights[delta]) * F(b))
        for h, delta in products
        for n, b in type_weights.items()
        if gcd(h * delta * n, g * p) == 1
    )
    units = tuple(z for z in range(g) if gcd(z, g) == 1)
    direct = {x: [F(0)] * g for x in range(1, p)}
    grouped = {x: [F(0)] * g for x in range(1, p)}

    # Original CRT ratio convolution, with s=p*z before common Fourier.
    for x in direct:
        for z in units:
            phase = (
                phase_label * pow(p * p * z, -1, g) - frequency * z
            ) % g
            for m, n, weight in terms:
                if (m + p * z * n) % g == 0 and (m + x * n) % p == 0:
                    direct[x][phase] += weight

    # Eliminate the common ratio and the active residue independently.
    inv_p = pow(p, -1, g)
    for m, n, weight in terms:
        x = -m * pow(n, -1, p) % p
        phase = inv_p * (
            -phase_label * n * pow(m, -1, g)
            + frequency * m * pow(n, -1, g)
        ) % g
        grouped[x][phase] += weight

    def freeze(values: dict[int, list[F]]) -> dict[int, tuple[F, ...]]:
        return {x: tuple(row) for x, row in values.items()}

    def center(values: dict[int, list[F]]) -> dict[int, tuple[F, ...]]:
        mean = tuple(
            sum((row[k] for row in values.values()), F(0)) / (p - 1)
            for k in range(g)
        )
        return {
            x: tuple(value - mean[k] for k, value in enumerate(row))
            for x, row in values.items()
        }

    return CommonFrequencyProfile(
        direct_raw=freeze(direct),
        raw=freeze(grouped),
        direct_centered=center(direct),
        centered=center(grouped),
        retained_products=products,
    )


def canonical_short_profile_lift(
    modulus: int, centered_profile: dict[int, F]
) -> dict[tuple[int, int], F]:
    """Minimal graph-span lift of a real centered short profile.

    Pairing this lift with K_c gives profile(-inverse(c)).
    Its squared norm is sum(profile**2)/phi(modulus), not the
    generally larger norm of an unprojected F tensor G.
    """
    q = modulus
    if q < 2:
        raise ValueError("modulus must be at least two")
    units = tuple(u for u in range(1, q) if gcd(u, q) == 1)
    if any(x not in units for x in centered_profile):
        raise ValueError("profile coordinates must be canonical unit residues")
    profile = {u: F(centered_profile.get(u, 0)) for u in units}
    if sum(profile.values(), F(0)) != 0:
        raise ValueError("the short profile must already be centered")
    return {
        (u, v): profile[-u * pow(v, -1, q) % q] / len(units)
        for u in units for v in units
    }


def common_zero_projection_norm_squared(g: int, cutoff: int) -> F:
    """Exact norm^2 of normalized common-zero row restricted by conductor.

    The input is counted in l2(U(g)); the Fourier output uses 1/sqrt(g).
    This is a coefficient-independent finite contraction, not a new
    estimate for the full coupled operator.
    """
    if g < 2 or mobius(g) == 0 or cutoff < 1:
        raise ValueError("squarefree g>=2 and positive conductor cutoff required")
    phi_g = sum(gcd(n, g) == 1 for n in range(1, g))
    numerator = 0
    for conductor in range(1, min(g, cutoff) + 1):
        if g % conductor:
            continue
        primitive_count = 1
        remaining = conductor
        prime = 2
        while prime * prime <= remaining:
            if remaining % prime == 0:
                primitive_count *= prime - 2
                remaining //= prime
            prime += 1
        if remaining > 1:
            primitive_count *= remaining - 2
        numerator += conductor * primitive_count
    return F(numerator, g * phi_g)


def common_zero_projection_polytope(
    *,
    common_exponent: F,
    left_common_cutoff_exponent: F,
    right_common_cutoff_exponent: F,
    required_linear_gain: F,
) -> dict[str, object]:
    """Compare the proved common-zero contraction with the row baseline.

    Only the two active-cofactor margins already used in eta_imb may be
    included in required_linear_gain.  A margin for g/cond(eta) is NOT
    additionally subtracted here.  The result covers this selected
    common-zero sector, never its complement or the full gate.
    """
    gamma = F(common_exponent)
    left, right = F(left_common_cutoff_exponent), F(right_common_cutoff_exponent)
    required = F(required_linear_gain)
    if min(gamma, left, right, required) < 0 or max(left, right) > gamma:
        raise ValueError("common cutoffs must lie between zero and gamma")
    gain = 2 * gamma - left - right
    return {
        "additional_linear_gain": gain,
        "required_linear_gain": required,
        "covered_common_zero_sector": gain >= required,
        "all_common_frequencies_covered": False,
        "coupled_kernel_gate_closed": False,
    }
