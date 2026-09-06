"""Finite common-frequency adapter; no analytic gate is asserted.

The rational profiles lie in Q[z]/(z**g - 1); joint kernels and Gram
checks use numerical complex evaluation. Input type_weights already
contains its Mobius or exact Type coefficient. The profile's common
outer scalar mu(g*p) is not included; fiber weights are supplied explicitly.
"""

from cmath import exp
from dataclasses import dataclass
from fractions import Fraction as F
from math import gcd, isqrt, pi, prod, sqrt

from scripts.mwkf_mobius_type_identity import divisors as integer_divisors, mobius


@dataclass(frozen=True)
class JointCommonFrequencyKernel:
    units: tuple[int, ...]
    full: tuple[tuple[complex, ...], ...]
    zero: tuple[tuple[complex, ...], ...]
    nonzero: tuple[tuple[complex, ...], ...]


@dataclass(frozen=True)
class CommonFrequencyGram:
    units: tuple[int, ...]
    shift_difference: int
    full: tuple[tuple[complex, ...], ...]
    full_zero: tuple[tuple[complex, ...], ...]
    zero_full: tuple[tuple[complex, ...], ...]
    zero_zero: tuple[tuple[complex, ...], ...]
    nonzero: tuple[tuple[complex, ...], ...]


def common_frequency_gram_kernel(
    *, common_modulus: int, left_shift: int, right_shift: int,
    left_phase: int, right_phase: int,
) -> CommonFrequencyGram:
    """Eliminate the shared intermediate unit, not the whole residue ring.

    Endpoint phases are the coefficients of 1/z (already scaled by
    inverse active squares). The same intermediate unit phase on the
    two edges cancels. Return all four terms of (J1-J10)(J2-J20)*.
    Evaluation is numerical; the finite identity is proved in CT1--CT4.
    """
    g = common_modulus
    if g < 2 or mobius(g) == 0:
        raise ValueError("common modulus must be squarefree and at least two")
    if gcd(left_phase, g) != 1 or gcd(right_phase, g) != 1:
        raise ValueError("both inverse-phase residues must be units")
    units = tuple(z for z in range(g) if gcd(z, g) == 1)
    a, b = left_shift % g, right_shift % g
    matrices = {name: [] for name in
                ("full", "full_zero", "zero_full", "zero_zero", "nonzero")}
    for z in units:
        rows = {name: [] for name in matrices}
        for v in units:
            exponent = (left_phase * pow(z, -1, g)
                        - right_phase * pow(v, -1, g)) % g
            phase = exp(2j * pi * exponent / g)
            left_unit = int(gcd(z - a, g) == 1)
            right_unit = int(gcd(v - b, g) == 1)
            full = int((z - v - a + b) % g == 0) * left_unit
            fz, zf, zz = left_unit / g, right_unit / g, len(units) / g**2
            values = (full, fz, zf, zz, full - fz - zf + zz)
            for name, value in zip(matrices, values):
                rows[name].append(phase * value)
        for name in matrices:
            matrices[name].append(tuple(rows[name]))
    return CommonFrequencyGram(units, (a - b) % g,
                               **{name: tuple(value) for name, value in matrices.items()})


def centered_common_fiber_energy(
    *, common_modulus: int, short_prime: int, determinant: int,
    profiles: dict[int, tuple[complex, ...]], phases: dict[int, int],
    weights: dict[int, complex], part: str,
) -> dict[str, object]:
    """Finite CT5--CT8: sum long levels before centering/squaring.

    Each input row is already evaluated at D/q modulo its long prime,
    and retains its own Type/h-delta coefficients. No analytic norm
    transfer from arbitrary rows to physical occupation is asserted.
    Empty supports return zero. All sums use exactly the supplied support.
    """
    g, q, d = common_modulus, short_prime, determinant
    if g < 2 or mobius(g) == 0:
        raise ValueError("common modulus must be squarefree and at least two")
    if q < 2 or any(q % k == 0 for k in range(2, isqrt(q) + 1)):
        raise ValueError("short modulus must be prime")
    if gcd(q, g) != 1 or gcd(d, q) != 1:
        raise ValueError("short modulus must be coprime to common modulus and determinant")
    if part not in ("full", "zero", "nonzero"):
        raise ValueError("part must be full, zero, or nonzero")
    if profiles.keys() != phases.keys() or profiles.keys() != weights.keys():
        raise ValueError("profile, phase and weight supports must agree")
    units = tuple(z for z in range(g) if gcd(z, g) == 1)
    size = len(units)
    shifts, residues, kernels = {}, {}, {}
    output = [[0j] * size for _ in range(q - 1)]
    for p, row in profiles.items():
        if p < 2 or any(p % k == 0 for k in range(2, isqrt(p) + 1)):
            raise ValueError("long moduli must be primes")
        if gcd(p, g*q*d) != 1 or len(row) != size:
            raise ValueError("invalid long modulus or common profile length")
        shifts[p] = d * pow(p*q, -1, g) % g
        residues[p] = -d * pow(p, -1, q) % q
        kernels[p] = getattr(joint_common_frequency_kernel(
            common_modulus=g, left_phase=phases[p], right_phase=1,
            shift=shifts[p]), part)
        for w in range(size):
            output[residues[p]-1][w] += weights[p] * sum(
                row[z] * kernels[p][z][w] for z in range(size))
    means = [sum(row[w] for row in output) / (q-1) for w in range(size)]
    direct = sum(abs(row[w]-means[w])**2 for row in output for w in range(size))
    diagonal, offdiagonal, density = 0j, 0j, 0j
    nonzero_shifts = set()
    for p1, row1 in profiles.items():
        for p2, row2 in profiles.items():
            gram = common_frequency_gram_kernel(
                common_modulus=g, left_shift=shifts[p1], right_shift=shifts[p2],
                left_phase=phases[p1], right_phase=phases[p2])
            matrix = getattr(gram, "zero_zero" if part == "zero" else part)
            value = weights[p1] * complex(weights[p2]).conjugate() * sum(
                row1[z] * complex(row2[v]).conjugate() * matrix[z][v]
                for z in range(size) for v in range(size))
            density += value / (q-1)
            if p1 == p2:
                diagonal += value
            elif (p2-p1) % q == 0:
                offdiagonal += value
                nonzero_shifts.add((p2-p1)//q)
    return {
        "direct_energy": direct,
        "expanded_energy": diagonal + offdiagonal - density,
        "diagonal": diagonal, "incident_offdiagonal": offdiagonal,
        "density": density.real, "nonzero_shifts": tuple(sorted(nonzero_shifts)),
        "physical_saving_proved": False,
    }


def induced_shift_gcd_histogram(
    *, common_modulus: int, determinant: int, shift_cutoff: int,
) -> dict[str, object]:
    """Exact integer divisor-floor counts for gcd(g,D*j), 1 <= j <= J.

    Counts are exact; the accompanying square-root Euler bound is only
    a floating-point evaluation of the analytically proved CT10 bound.
    This does not remove the length-J cost or normalize physical weights.
    """
    g, jmax = common_modulus, shift_cutoff
    if g < 1 or mobius(g) == 0 or jmax < 0:
        raise ValueError("squarefree positive modulus and nonnegative cutoff required")
    d0 = gcd(g, determinant)
    g0 = g // d0
    divisors = integer_divisors(g0)
    counts = {}
    for divisor in divisors:
        count = sum(mobius(e) * (jmax // (divisor*e))
                    for e in divisors if (g0//divisor) % e == 0)
        if count:
            counts[d0*divisor] = count
    primes = [k for k in divisors if k > 1 and
              not any(k % d == 0 for d in range(2, isqrt(k)+1))]
    bound = jmax * sqrt(d0) * prod(1 + (sqrt(p)-1)/p for p in primes)
    return {"counts": counts, "euler_upper_bound": bound}


def joint_common_frequency_kernel(
    *, common_modulus: int, left_phase: int, right_phase: int, shift: int
) -> JointCommonFrequencyKernel:
    """Numerical finite certificate for joint frequency reassembly.

    The physical pairing is Z_left.T @ K @ conjugate(Z_right).
    The full kernel is obtained from the partial shift, while nonzero
    is independently obtained by summing every nonzero Fourier mode.
    These floating-point matrices do not certify an analytic estimate.
    """
    g = common_modulus
    if g < 2 or mobius(g) == 0:
        raise ValueError("common modulus must be squarefree and at least two")
    if gcd(left_phase, g) != 1 or gcd(right_phase, g) != 1:
        raise ValueError("both inverse-phase residues must be units")
    units = tuple(z for z in range(g) if gcd(z, g) == 1)
    roots = tuple(exp(2j * pi * k / g) for k in range(g))
    full, zero, nonzero = [], [], []
    for z in units:
        full_row, zero_row, nonzero_row = [], [], []
        for w in units:
            phase = roots[(left_phase * pow(z, -1, g)
                           - right_phase * pow(w, -1, g)) % g]
            difference = (shift - z + w) % g
            full_row.append(phase if difference == 0 else 0j)
            zero_row.append(phase / g)
            nonzero_row.append(phase * sum(roots[nu * difference % g]
                                          for nu in range(1, g)) / g)
        full.append(tuple(full_row))
        zero.append(tuple(zero_row))
        nonzero.append(tuple(nonzero_row))
    return JointCommonFrequencyKernel(units, tuple(full), tuple(zero), tuple(nonzero))


def common_character_support_polytope(
    *,
    common_exponent: F,
    exceptional_gcd_exponent: F,
    left_support_exponent: F,
    right_support_exponent: F,
    required_linear_gain: F,
) -> dict[str, object]:
    """Combine small-common-family Weil with the registered active baseline.

    Supports are specified common character families, not conductor
    cutoffs and not counts that may be assumed for arbitrary physical
    coefficients.  This implication includes the full and the nonzero
    common-frequency sum.  No old Type-I gain is subtracted.
    """
    gamma, exceptional, left, right, required = map(F, (
        common_exponent, exceptional_gcd_exponent, left_support_exponent,
        right_support_exponent, required_linear_gain,
    ))
    if min(gamma, exceptional, left, right, required) < 0:
        raise ValueError("all exponents must be nonnegative")
    if max(exceptional, left, right) > gamma:
        raise ValueError("gcd and common support exponents cannot exceed g")
    gain = max(F(0), (gamma - exceptional - left - right) / 2)
    return {
        "additional_linear_gain": gain,
        "selected_sector_exponent_sufficient": gain >= required,
        "nonzero_common_frequency_complement_included": True,
        "unrestricted_common_character_family_covered": False,
        "coupled_kernel_gate_closed": False,
    }


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
