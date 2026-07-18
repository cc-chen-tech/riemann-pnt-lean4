from decimal import Decimal, localcontext
from fractions import Fraction

import pytest

from experiments.pnt.smoothed_error_optimizer import (
    Candidate,
    certified_log1p,
    compare_candidates,
    optimize_candidate,
)


def test_certified_log1p_contains_high_precision_reference():
    enclosure = certified_log1p(Fraction(1, 2), precision=60)
    with localcontext() as context:
        context.prec = 80
        reference = Decimal("1.5").ln()

    assert enclosure.lower <= reference <= enclosure.upper
    assert enclosure.lower > 0
    assert enclosure.upper - enclosure.lower < Decimal("1e-58")


def test_finite_height_envelope_is_exact_before_decimal_conversion():
    candidate = Candidate(
        name="finite-height",
        model="finite_height",
        constant=Fraction(3, 2),
    )

    enclosure = candidate.smoothed_error(x=12, height=9, precision=60)

    assert enclosure.lower == Decimal(24)
    assert enclosure.upper == Decimal(24)


def test_classical_zero_free_interval_is_ambient_context_independent():
    candidate = Candidate(
        name="classical-zero-free",
        model="classical_zero_free",
        constant=Fraction(1),
        decay=Fraction(1, 5),
    )

    with localcontext() as context:
        context.prec = 7
        low_ambient_precision = candidate.smoothed_error(
            x=1_000_000, height=1_000_000, precision=80
        )
    with localcontext() as context:
        context.prec = 43
        high_ambient_precision = candidate.smoothed_error(
            x=1_000_000, height=1_000_000, precision=80
        )
    with localcontext() as context:
        context.prec = 200
        x = Decimal(1_000_000)
        reference = x * (-(Decimal(1) / Decimal(5)) * x.ln().sqrt()).exp()

    assert low_ambient_precision == high_ambient_precision
    assert low_ambient_precision.lower <= reference <= low_ambient_precision.upper


def test_candidate_records_identity_approximation_scope():
    candidate = Candidate("finite-height", "finite_height", Fraction(1))

    assert candidate.as_dict()["approximation"] == "identity"


def test_optimizer_selects_the_smallest_certified_upper_bound():
    candidate = Candidate(
        name="zero-error",
        model="finite_height",
        constant=Fraction(0),
    )

    result = optimize_candidate(
        candidate=candidate,
        x=100,
        height=100,
        h_values=[1, 5, 20],
        precision=60,
    )

    assert result.selected.h == 1
    assert result.selected.upper_bound == min(item.upper_bound for item in result.evaluations)


def test_comparison_is_deterministic_and_precision_stable():
    candidates = [
        Candidate("finite-height", "finite_height", Fraction(1, 10)),
        Candidate("rh", "rh", Fraction(1, 100)),
        Candidate("classical-zero-free", "classical_zero_free", Fraction(2), Fraction(1, 5)),
    ]
    arguments = dict(x=10_000, height=1_000_000, h_values=[10, 20, 40, 80, 160])

    report_60 = compare_candidates(candidates=candidates, precision=60, **arguments)
    report_90 = compare_candidates(candidates=candidates, precision=90, **arguments)

    assert report_60.schema == "smoothed-error-comparison-v1"
    assert report_60.to_json() == compare_candidates(
        candidates=candidates, precision=60, **arguments
    ).to_json()
    assert [item.selected.h for item in report_60.results] == [
        item.selected.h for item in report_90.results
    ]
    assert report_60.winner == report_90.winner


def test_candidate_parameters_are_validated():
    with pytest.raises(ValueError, match="positive decay"):
        Candidate("bad", "classical_zero_free", Fraction(1), Fraction(0))
