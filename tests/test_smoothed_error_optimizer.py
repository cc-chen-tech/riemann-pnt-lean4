from decimal import Decimal, localcontext
from fractions import Fraction

import pytest

from experiments.pnt.smoothed_error_optimizer import (
    ApproximationDifferences,
    Candidate,
    Interval,
    certified_log1p,
    compare_candidates,
    main,
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


def test_identity_approximation_matches_certified_point_intervals():
    candidate = Candidate("zero-error", "finite_height", Fraction(0))
    arguments = dict(
        candidate=candidate,
        x=100,
        height=100,
        h_values=[1, 5, 20],
        precision=60,
    )

    identity = optimize_candidate(
        approximation=ApproximationDifferences.identity(), **arguments
    )
    certified = optimize_candidate(
        approximation=ApproximationDifferences.certified(
            (h, Interval(Decimal(h), Decimal(h))) for h in [20, 1, 5]
        ),
        **arguments,
    )

    assert identity == certified


def test_optimizer_uses_signed_certified_difference_instead_of_h():
    candidate = Candidate("zero-error", "finite_height", Fraction(0))

    identity = optimize_candidate(
        candidate=candidate,
        x=100,
        height=100,
        h_values=[10],
        approximation=ApproximationDifferences.identity(),
        precision=60,
    )
    adversarial = optimize_candidate(
        candidate=candidate,
        x=100,
        height=100,
        h_values=[10],
        approximation=ApproximationDifferences.certified(
            [(10, Interval(Decimal("-1"), Decimal("0")))]
        ),
        precision=60,
    )

    assert adversarial.selected.approximation_difference == Interval(
        Decimal("-1"), Decimal("0")
    )
    assert adversarial.selected.approximation_bias_upper > Decimal(100)
    assert adversarial.selected.upper_bound > identity.selected.upper_bound


def test_certified_differences_must_cover_exactly_the_optimized_widths():
    candidate = Candidate("zero-error", "finite_height", Fraction(0))
    approximation = ApproximationDifferences.certified(
        [(1, Interval(Decimal(1), Decimal(1)))]
    )

    with pytest.raises(ValueError, match="missing h values: 2"):
        optimize_candidate(
            candidate=candidate,
            x=100,
            height=100,
            h_values=[1, 2],
            approximation=approximation,
            precision=60,
        )

    with pytest.raises(ValueError, match="unused h values: 1"):
        optimize_candidate(
            candidate=candidate,
            x=100,
            height=100,
            h_values=[2],
            approximation=ApproximationDifferences.certified(
                [
                    (1, Interval(Decimal(1), Decimal(1))),
                    (2, Interval(Decimal(2), Decimal(2))),
                ]
            ),
            precision=60,
        )


def test_certified_differences_reject_duplicate_widths():
    with pytest.raises(ValueError, match="duplicate h value: 10"):
        ApproximationDifferences.certified(
            [
                (10, Interval(Decimal(9), Decimal(11))),
                (10, Interval(Decimal(8), Decimal(12))),
            ]
        )


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
        approximation=ApproximationDifferences.identity(),
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
    arguments = dict(
        x=10_000,
        height=1_000_000,
        h_values=[10, 20, 40, 80, 160],
        approximation=ApproximationDifferences.identity(),
    )

    report_60 = compare_candidates(candidates=candidates, precision=60, **arguments)
    report_90 = compare_candidates(candidates=candidates, precision=90, **arguments)

    assert report_60.schema == "smoothed-error-comparison-v2"
    assert report_60.to_json() == compare_candidates(
        candidates=candidates, precision=60, **arguments
    ).to_json()
    assert [item.selected.h for item in report_60.results] == [
        item.selected.h for item in report_90.results
    ]
    assert report_60.winner == report_90.winner


def test_v2_json_serializes_approximation_once_in_sorted_order():
    candidate = Candidate("zero-error", "finite_height", Fraction(0))
    approximation = ApproximationDifferences.certified(
        [
            (20, Interval(Decimal("19.5"), Decimal("20.5"))),
            (10, Interval(Decimal("9"), Decimal("11"))),
        ]
    )
    report = compare_candidates(
        candidates=[candidate],
        x=100,
        height=100,
        h_values=[20, 10],
        approximation=approximation,
        precision=60,
    )
    payload = __import__("json").loads(report.to_json())

    assert payload["schema"] == "smoothed-error-comparison-v2"
    assert payload["approximation"] == {
        "mode": "certified_intervals",
        "quantity": "Re(A_T(x+h)-A_T(x))",
        "real_difference_intervals": [
            {"h": 10, "lower": "9", "upper": "11"},
            {"h": 20, "lower": "19.5", "upper": "20.5"},
        ],
    }
    assert "approximation" not in payload["results"][0]["candidate"]
    assert "approximation_difference" in payload["results"][0]["evaluations"][0]
    assert report.to_json() == compare_candidates(
        candidates=[candidate],
        x=100,
        height=100,
        h_values=[10, 20],
        approximation=ApproximationDifferences.certified(
            reversed(approximation.differences)
        ),
        precision=60,
    ).to_json()


def test_cli_requires_an_explicit_approximation_mode(capsys):
    base = [
        "--x", "100", "--height", "100", "--h", "10",
        "--candidate", "zero:finite_height:0", "--precision", "30",
    ]

    with pytest.raises(SystemExit):
        main(base)

    main([*base, "--identity-approximation"])
    payload = __import__("json").loads(capsys.readouterr().out)
    assert payload["approximation"]["mode"] == "identity"


def test_candidate_parameters_are_validated():
    with pytest.raises(ValueError, match="positive decay"):
        Candidate("bad", "classical_zero_free", Fraction(1), Fraction(0))
