"""Tests for the rigorous arb interval assembly of the auxiliary S/CC/XC route.

The committed reference artifacts (256 nominal bits) are validated against the
frozen high-precision cross-check record
``groskin_2607_02828_v1_small_n_high_precision_crosscheck.json``.

Containment convention: the frozen record serializes two point values per
matrix entry -- a 70-significant-digit headline (``auxiliary_closed_form``)
and a 130-significant-digit audit serialization
(``auxiliary_closed_form_high_precision_audit``).  The emitted intervals are
far tighter than half an ulp of the 70-digit headline (radii ~1e-80 at 256
bits), so strict enclosure is asserted against the 130-digit audit value, the
only frozen serialization finer than the interval radius.  The 70-digit
headline is asserted to lie within its own serialization rounding radius of
the interval (half an ulp at 70 digits, the same rounding-radius formula the
frozen artifact's own verifier uses), which is the strongest statement the
headline serialization can support.
"""

import copy
import json
from decimal import Decimal, localcontext
from pathlib import Path

import pytest

from experiments.rh import weil_extremal_crosscheck as crosscheck
from experiments.rh import weil_extremal_interval_auxiliary as interval_aux


ROOT = Path(__file__).parents[1]
REFERENCE_DIR = ROOT / "experiments" / "rh" / "reference"
FROZEN_CROSSCHECK = (
    REFERENCE_DIR / "groskin_2607_02828_v1_small_n_high_precision_crosscheck.json"
)
ARTIFACT_CASES = [(13, 4), (13, 8)]
ARTIFACT_PREC_BITS = 256
ARTIFACT_PATHS = {
    case: REFERENCE_DIR
    / interval_aux.artifact_filename(case[0], case[1], ARTIFACT_PREC_BITS)
    for case in ARTIFACT_CASES
}
HEADLINE_SERIALIZED_DIGITS = 70
RADIUS_BOUND = Decimal("1e-60")


def _load(path):
    return json.loads(path.read_bytes())


def _entry_interval(record, i, j):
    dimension = record["dimension"]
    index = (i + record["N"]) * dimension + (j + record["N"])
    lo, hi = record["entries"][index]
    return Decimal(lo), Decimal(hi)


def _decimal_difference(left, right):
    """Exact-scale Decimal difference independent of the ambient context.

    Plain Decimal arithmetic rounds to the ambient context precision (28
    significant digits by default); interval widths and escape distances are
    tiny differences of 80-digit numbers, so they are computed here under a
    sufficiently wide local context.
    """
    with localcontext() as context:
        context.prec = 120
        return left - right


def _frozen_case(frozen, c, N):
    matches = [case for case in frozen["cases"] if case["c"] == c and case["N"] == N]
    assert len(matches) == 1
    return matches[0]


# ---------------------------------------------------------------------------
# Committed reference artifacts: schema, hashing, radii, symmetry.
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("case", ARTIFACT_CASES)
def test_reference_artifact_schema_and_integrity(case):
    path = ARTIFACT_PATHS[case]
    assert path.is_file(), f"missing committed artifact: {path}"
    assert interval_aux.verify_interval_artifact_file(path)
    record = _load(path)
    c, N = case
    assert record["schema_version"] == "weil-extremal-kernel-interval-assembly/v1"
    assert record["route"] == "auxiliary_closed_form_interval_arb"
    assert record["index_convention"] == "fourier -N..N row-major"
    assert record["c"] == c and record["N"] == N
    assert record["prec_bits"] == ARTIFACT_PREC_BITS
    assert record["dimension"] == 2 * N + 1
    assert len(record["entries"]) == (2 * N + 1) ** 2
    for entry in record["entries"]:
        assert isinstance(entry, list) and len(entry) == 2
        lo, hi = Decimal(entry[0]), Decimal(entry[1])
        assert lo.is_finite() and hi.is_finite()
        assert lo <= hi


@pytest.mark.parametrize("case", ARTIFACT_CASES)
def test_reference_artifact_radius_bound(case):
    record = _load(ARTIFACT_PATHS[case])
    widths = [_decimal_difference(Decimal(hi), Decimal(lo)) for lo, hi in record["entries"]]
    assert all(width >= 0 for width in widths)
    assert max(widths) / 2 < RADIUS_BOUND


@pytest.mark.parametrize("case", ARTIFACT_CASES)
def test_reference_artifact_symmetric_entries_overlap(case):
    record = _load(ARTIFACT_PATHS[case])
    N = record["N"]
    for i in range(-N, N + 1):
        for j in range(-N, N + 1):
            lo_ij, hi_ij = _entry_interval(record, i, j)
            lo_ji, hi_ji = _entry_interval(record, j, i)
            assert max(lo_ij, lo_ji) <= min(hi_ij, hi_ji), (
                f"symmetric entries ({i},{j}) and ({j},{i}) do not overlap"
            )


# ---------------------------------------------------------------------------
# Hard correctness gate: containment of the frozen point values.
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("case", ARTIFACT_CASES)
def test_reference_artifact_contains_frozen_point_values(case):
    c, N = case
    record = _load(ARTIFACT_PATHS[case])
    frozen_case = _frozen_case(_load(FROZEN_CROSSCHECK), c, N)
    assert frozen_case["entry_count"] == record["dimension"] ** 2
    for frozen_entry in frozen_case["entries"]:
        i, j = frozen_entry["i"], frozen_entry["j"]
        lo, hi = _entry_interval(record, i, j)
        audit_point = Decimal(frozen_entry["auxiliary_closed_form_high_precision_audit"])
        assert lo <= audit_point <= hi, (
            f"130-digit frozen audit point at ({i},{j}) escapes [{lo}, {hi}]"
        )


@pytest.mark.parametrize("case", ARTIFACT_CASES)
def test_reference_artifact_headline_consistent_within_serialization(case):
    """The 70-digit headline point must lie within half an ulp of the interval."""
    c, N = case
    record = _load(ARTIFACT_PATHS[case])
    frozen_case = _frozen_case(_load(FROZEN_CROSSCHECK), c, N)
    for frozen_entry in frozen_case["entries"]:
        i, j = frozen_entry["i"], frozen_entry["j"]
        lo, hi = _entry_interval(record, i, j)
        headline = Decimal(frozen_entry["auxiliary_closed_form"])
        distance = max(
            _decimal_difference(lo, headline),
            _decimal_difference(headline, hi),
            Decimal(0),
        )
        rounding_radius = Decimal(5).scaleb(
            headline.adjusted() - HEADLINE_SERIALIZED_DIGITS
        )
        assert distance <= rounding_radius, (
            f"70-digit headline at ({i},{j}) is {distance} from the interval, "
            f"beyond its serialization rounding radius {rounding_radius}"
        )


# ---------------------------------------------------------------------------
# Fresh assembly semantics: interval route vs the mpmath point route.
# ---------------------------------------------------------------------------


def test_interval_route_encloses_mpmath_point_route():
    c, N, prec_bits = 13, 4, 192
    matrix = interval_aux.assemble_auxiliary_interval(c, N, prec_bits)
    points = crosscheck.assemble_auxiliary_closed_form(c, N, 100)
    assert set(matrix) == set(points)
    mp = crosscheck._mpmath()
    for key, ball in matrix.items():
        lo, hi = interval_aux._export_ball(ball)
        point = Decimal(mp.nstr(points[key], 90))
        assert Decimal(lo) <= point <= Decimal(hi), (
            f"mpmath point at {key} escapes the interval"
        )
        assert _decimal_difference(Decimal(hi), Decimal(lo)) / 2 < RADIUS_BOUND


# ---------------------------------------------------------------------------
# Export primitives: outward rounding is rigorous.
# ---------------------------------------------------------------------------


def test_export_ball_outward_rounding():
    from flint import arb, ctx, fmpq

    previous = ctx.prec
    ctx.prec = 128
    try:
        pi_reference = Decimal(
            "3.1415926535897932384626433832795028841971693993751058209749445923"
        )
        lo, hi = interval_aux._export_ball(arb.pi())
        assert Decimal(lo) < pi_reference < Decimal(hi)
        assert _decimal_difference(Decimal(hi), Decimal(lo)) < Decimal("1e-30")

        # Unary minus on a Decimal applies context rounding (28 digits by
        # default); copy_negate() is the exact negation.
        negative_pi = pi_reference.copy_negate()
        lo, hi = interval_aux._export_ball(-arb.pi())
        assert Decimal(lo) < negative_pi < Decimal(hi)

        assert interval_aux._export_ball(arb(0)) == ("0", "0")

        lo, hi = interval_aux._export_ball(arb(1, fmpq(1, 10)))
        assert Decimal(lo) <= Decimal("0.9")
        assert Decimal(hi) >= Decimal("1.1")
        assert _decimal_difference(Decimal(hi), Decimal(lo)) < Decimal("0.21")
    finally:
        ctx.prec = previous


def test_verify_interval_artifact_rejects_tampering(tmp_path):
    record = interval_aux.build_interval_artifact(13, 2, 128)
    assert interval_aux.verify_interval_artifact(record)

    tampered = copy.deepcopy(record)
    lo, hi = tampered["entries"][0]
    tampered["entries"][0] = [hi, lo]
    assert not interval_aux.verify_interval_artifact(tampered)

    tampered = copy.deepcopy(record)
    tampered["entries"][0][0] = "12345"
    assert not interval_aux.verify_interval_artifact(tampered)

    tampered = copy.deepcopy(record)
    tampered["dimension"] += 1
    assert not interval_aux.verify_interval_artifact(tampered)


# ---------------------------------------------------------------------------
# CLI smoke test.
# ---------------------------------------------------------------------------


def test_cli_emits_valid_artifact(tmp_path):
    out = tmp_path / "interval.json"
    status = interval_aux.main(
        ["--c", "13", "--N", "2", "--prec-bits", "128", "--out", str(out)]
    )
    assert status == 0
    assert interval_aux.verify_interval_artifact_file(out)
    record = _load(out)
    assert record["dimension"] == 5
    assert len(record["entries"]) == 25
    assert record["prec_bits"] == 128
