"""Regressions for the phase dropped between the two CRT descents."""

import cmath
import sys
from fractions import Fraction as F
from math import gcd
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.mwkf_common_phase_adapter import common_frequency_profile
from scripts.mwkf_mobius_type_identity import divisors, mobius


def row(**updates):
    args = dict(
        common_modulus=5, active_prime=7, phase_label=3, frequency=0,
        h_weights={1: F(1)}, delta_weights={1: F(1)}, type_weights={1: F(1)},
    )
    args.update(updates)
    return common_frequency_profile(**args)


def test_zero_common_frequency_retains_inverse_ratio_phase():
    r = row()
    assert r.raw[6] == (F(0), F(1), F(0), F(0), F(0))
    assert r.centered[6] == (F(0), F(5, 6), F(0), F(0), F(0))
    assert r.centered[1] == (F(0), F(-1, 6), F(0), F(0), F(0))
    assert r.direct_centered == r.centered


def test_nonzero_common_frequency_retains_the_other_ratio():
    # z=-1/7=2 mod 5; original phase at frequency one is 1-2=4.
    assert row(frequency=1).raw[6] == (F(0), F(0), F(0), F(0), F(1))


@pytest.mark.parametrize("g,p", [(2, 3), (3, 5), (5, 7), (6, 5), (15, 7)])
@pytest.mark.parametrize("frequency", [-2, 0, 1, 8])
def test_crt_sum_and_eliminated_multiplier_agree(g, p, frequency):
    r = row(
        common_modulus=g, active_prime=p, phase_label=-1, frequency=frequency,
        h_weights={-2: F(3), 1: F(2), 5: F(-1)},
        delta_weights={1: F(1), 2: F(-2), 3: F(1, 2)},
        type_weights={n: F(mobius(n), n) for n in range(1, 19)},
    )
    assert r.direct_raw == r.raw
    assert r.direct_centered == r.centered
    assert set(r.retained_products) == {
        (h, delta) for h in (-2, 1, 5) for delta in (1, 2, 3)
    }
    assert all(sum(values[k] for values in r.centered.values()) == 0
               for k in range(g))


def test_unit_masks_are_not_deleted_when_the_character_conductor_descends():
    assert row(h_weights={5: F(1)}).raw == {x: (F(0),) * 5 for x in range(1, 7)}
    assert row(type_weights={7: F(-1)}).raw == {
        x: (F(0),) * 5 for x in range(1, 7)
    }


def test_type_reassembly_commutes_with_the_complete_multiplier():
    ns = (1, 2, 6, 22, 143)
    components = [{}, {}, {}]
    for n in ns:
        if n <= 3:
            values = (mobius(n), 0, 0)
        else:
            short = sum(
                mobius(b) * mobius(c)
                for b in divisors(n) for c in divisors(n // b)
                if b <= 3 and c <= 3
            )
            long = sum(
                mobius(b) * mobius(c)
                for b in divisors(n) for c in divisors(n // b)
                if b > 3 and c > 3
            )
            values = (0, -short, long)
        for coefficient, part in zip(values, components):
            part[n] = F(coefficient)
    args = dict(h_weights={1: F(1), 2: F(-1)}, delta_weights={1: F(1), 3: F(2)})
    raw = row(type_weights={n: F(mobius(n)) for n in ns}, **args)
    split = [row(type_weights=part, **args) for part in components]
    assert all(
        raw.centered[x][k] == sum(s.centered[x][k] for s in split)
        for x in raw.centered for k in range(5)
    )


def test_zero_frequency_multiplier_has_nonseparable_common_kernel():
    # A=-C/p=1 mod 5, evaluated on common m,n in {1,2}.
    # Determinant = zeta_5**2 - 1, not zero.
    vals = []
    zeta = cmath.exp(2j * cmath.pi / 5)
    for m in (1, 2):
        one_row = []
        for n in (1, 2):
            r = row(h_weights={m: F(1)}, type_weights={n: F(1)})
            value = sum(
                sum(float(c) * zeta**k for k, c in enumerate(poly))
                for poly in r.raw.values()
            )
            one_row.append(value)
        vals.append(one_row)
    determinant = vals[0][0] * vals[1][1] - vals[0][1] * vals[1][0]
    assert abs(determinant - (zeta**2 - 1)) < 1e-12
    assert abs(determinant) > 1


def test_empty_support_and_phase_periodicity():
    assert all(not any(v) for v in row(h_weights={}).centered.values())
    assert row(frequency=1).raw == row(frequency=6).raw
    assert row(phase_label=3).raw == row(phase_label=8).raw


@pytest.mark.parametrize("updates", [
    {"common_modulus": 4}, {"active_prime": 9},
    {"common_modulus": 7}, {"phase_label": 5},
    {"h_weights": {0: F(1)}}, {"delta_weights": {0: F(1)}},
    {"type_weights": {0: F(1)}},
])
def test_invalid_physical_coordinates_are_rejected(updates):
    with pytest.raises(ValueError):
        row(**updates)


@pytest.mark.parametrize("g", [3, 5, 7, 11])
def test_complete_common_multiplier_gram_has_exact_gauss_spectrum(g):
    # Independent analytic oracle: diagonal g-1, off-diagonal -1.
    p = next(p for p in (13, 17) if gcd(p, g) == 1)
    zeta = cmath.exp(2j * cmath.pi / g)
    matrix = []
    for m in range(1, g):
        matrix_row = []
        for n in range(1, g):
            r = row(common_modulus=g, active_prime=p, phase_label=-p,
                    h_weights={m: F(1)}, type_weights={n: F(1)})
            matrix_row.append(sum(
                sum(float(c) * zeta**k for k, c in enumerate(poly))
                for poly in r.raw.values()
            ))
        matrix.append(matrix_row)
    for a in range(g - 1):
        for b in range(g - 1):
            entry = sum(x * y.conjugate() for x, y in zip(matrix[a], matrix[b]))
            assert abs(entry - (g - 1 if a == b else -1)) < 1e-10


def test_canonical_graph_lift_has_the_exact_short_row_norm():
    from scripts.mwkf_common_phase_adapter import canonical_short_profile_lift
    r = {1: F(1), 2: F(-1), 3: F(2), 4: F(-2)}
    b = canonical_short_profile_lift(5, r)
    assert sum(value**2 for value in b.values()) == F(5, 2)
    for c in range(1, 5):
        pairing = sum(
            value * (F(int(v == c * u % 5)) - F(1, 4))
            for (u, v), value in b.items()
        )
        assert pairing == r[-pow(c, -1, 5) % 5]


def test_unprojected_tensor_is_not_a_ratio_row_subenergy():
    from scripts.mwkf_common_phase_adapter import canonical_short_profile_lift
    f = {1: F(1), 2: F(-1), 3: F(0), 4: F(0)}
    # G(v)=1: ratio convolution vanishes identically, but tensor norm^2=8.
    ratios = {
        c: sum(f[-c * v % 5] for v in range(1, 5))
        for c in range(1, 5)
    }
    assert ratios == {c: F(0) for c in range(1, 5)}
    assert sum(f[u]**2 for u in range(1, 5) for _ in range(1, 5)) == 8
    assert not any(canonical_short_profile_lift(5, ratios).values())


def test_canonical_graph_lift_is_the_orthogonal_projection():
    from scripts.mwkf_common_phase_adapter import canonical_short_profile_lift
    raw = {(u, v): F(u * v) for u in range(1, 5) for v in range(1, 5)}
    profile = {
        -pow(c, -1, 5) % 5: sum(
            val * (F(int(v == c * u % 5)) - F(1, 4))
            for (u, v), val in raw.items()
        )
        for c in range(1, 5)
    }
    projected = canonical_short_profile_lift(5, profile)
    residual = {k: raw[k] - projected[k] for k in raw}
    assert sum(residual[k] * projected[k] for k in raw) == 0
    assert sum(raw[k]**2 for k in raw) == (
        sum(residual[k]**2 for k in raw) + sum(projected[k]**2 for k in raw)
    )


@pytest.mark.parametrize("q,profile", [
    (1, {}), (5, {0: F(1)}), (5, {1: F(1)}),
])
def test_graph_lift_rejects_noncentered_or_nonunit_data(q, profile):
    from scripts.mwkf_common_phase_adapter import canonical_short_profile_lift
    with pytest.raises(ValueError):
        canonical_short_profile_lift(q, profile)


def test_type_I_coverage_refuses_an_unverified_common_phase_deletion():
    from scripts.audit_mwkf_coverage import prime_incidence_short_type_I_pv_polytope_audit
    result = prime_incidence_short_type_I_pv_polytope_audit(
        internal_type_length_exponent=F(3),
        first_short_cutoff_exponent=F(1, 2),
        second_short_cutoff_exponent=F(1, 2),
        long_active_primitive_conductor_exponent=F(2),
        short_active_primitive_conductor_exponent=F(3, 2),
        long_active_imprimitive_cofactor_exponent=F(0),
        short_active_imprimitive_cofactor_exponent=F(0),
        short_companion_factor_exponent=F(1, 2),
        physical_maximum_primitive_conductor_exponent=F(2),
        packet_exhaustive_residual_bv_adapter_verified=True,
    )
    assert not result["covered_type_I_short_companion_subpolytope"]
    assert result["type_I_cell_retained_in_PCDI_SREM"]
    assert result["usable_bilinear_gain_exponent"] == 0
    assert result["remaining_companion_dispersion_gain_exponent"] == F(1, 4)


@pytest.mark.parametrize("g,cutoff,want", [
    (5, 1, F(1, 20)), (5, 5, F(4, 5)),
    (6, 2, F(1, 12)), (6, 6, F(1, 3)),
    (15, 3, F(1, 30)), (15, 5, F(19, 120)), (15, 15, F(8, 15)),
])
def test_common_zero_projection_budget(g, cutoff, want):
    from scripts.mwkf_common_phase_adapter import common_zero_projection_norm_squared
    assert common_zero_projection_norm_squared(g, cutoff) == want


def test_projection_norm_matches_direct_character_squares_mod_15():
    from scripts.mwkf_common_phase_adapter import common_zero_projection_norm_squared
    units = tuple(s for s in range(15) if gcd(s, 15) == 1)
    log3, log5 = {1: 0, 2: 1}, {1: 0, 2: 1, 4: 2, 3: 3}
    for cutoff in (1, 3, 5, 15):
        direct = 0.0
        for k in range(2):
            for j in range(4):
                conductor = (3 if k else 1) * (5 if j else 1)
                if conductor > cutoff:
                    continue
                total = sum(
                    cmath.exp(2j * cmath.pi * (
                        F(pow(s, -1, 15), 15)
                        + F(k * log3[s % 3], 2) + F(j * log5[s % 5], 4)
                    ))
                    for s in units
                )
                direct += abs(total)**2 / (15 * 8)
        assert abs(direct - float(common_zero_projection_norm_squared(15, cutoff))) < 1e-12


@pytest.mark.parametrize("gamma,left,right,covered", [
    (F(1), F(0), F(1), True),
    (F(1), F(1), F(1), False),
    (F(1, 4), F(0), F(1, 4), True),
    (F(1, 5), F(0), F(1, 5), False),
])
def test_common_zero_low_conductor_sector_coverage(gamma, left, right, covered):
    from scripts.mwkf_common_phase_adapter import common_zero_projection_polytope
    r = common_zero_projection_polytope(
        common_exponent=gamma,
        left_common_cutoff_exponent=left,
        right_common_cutoff_exponent=right,
        required_linear_gain=F(1, 4),
    )
    assert r["covered_common_zero_sector"] is covered
    assert r["additional_linear_gain"] == 2 * gamma - left - right
    assert not r["all_common_frequencies_covered"]
    assert not r["coupled_kernel_gate_closed"]


@pytest.mark.parametrize("g,cutoff", [(4, 2), (5, 0), (1, 1)])
def test_common_zero_projection_rejects_invalid_modulus_or_cutoff(g, cutoff):
    from scripts.mwkf_common_phase_adapter import common_zero_projection_norm_squared
    with pytest.raises(ValueError):
        common_zero_projection_norm_squared(g, cutoff)
