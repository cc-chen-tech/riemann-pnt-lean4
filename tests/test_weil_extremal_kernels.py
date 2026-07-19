import hashlib
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import pytest

from experiments.rh import weil_extremal_kernels as weil


REFERENCE_PROVENANCE = (
    Path(__file__).parents[1]
    / "experiments"
    / "rh"
    / "reference"
    / "groskin_2607_02828_v1_c100_N200_provenance.json"
)


def refresh_payload_digest(record):
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    canonical_payload = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    )
    record["payload_sha256"] = hashlib.sha256(
        canonical_payload.encode("utf-8")
    ).hexdigest()


def test_finite_dictionary_dimensions_distinguish_full_and_even_sector():
    assert weil.finite_dictionary_dimensions(200) == weil.FiniteDictionaryDimensions(
        fourier_cutoff=200,
        full_dimension=401,
        even_sector_dimension=201,
    )
    assert weil.finite_dictionary_dimensions(250) == weil.FiniteDictionaryDimensions(
        fourier_cutoff=250,
        full_dimension=501,
        even_sector_dimension=251,
    )
    with pytest.raises(ValueError, match="nonnegative integer"):
        weil.finite_dictionary_dimensions(-1)


def test_released_groskin_provenance_is_dimensionally_self_consistent():
    source = REFERENCE_PROVENANCE.read_bytes()
    record = json.loads(source)

    assert hashlib.sha256(source).hexdigest() == (
        "5d14ea5bc0874c4edf15b586075337c1852b8e592bd7c4a7867ea14a995325a7"
    )
    assert weil.verify_groskin_provenance_metadata(
        record, expected_c=100, expected_N=200
    )

    wrong_sector_dimension = dict(record, dimension=201, n_pos=201)
    assert not weil.verify_groskin_provenance_metadata(
        wrong_sector_dimension, expected_c=100, expected_N=200
    )


def test_groskin_provenance_metadata_rejects_inertia_or_status_tampering():
    record = json.loads(REFERENCE_PROVENANCE.read_text(encoding="utf-8"))

    assert not weil.verify_groskin_provenance_metadata(
        dict(record, n_neg=1), expected_c=100, expected_N=200
    )
    assert not weil.verify_groskin_provenance_metadata(
        dict(record, certified_positive_definite=False),
        expected_c=100,
        expected_N=200,
    )


def test_cli_checks_released_groskin_provenance_metadata_only():
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "experiments.rh.weil_extremal_kernels",
            "verify-groskin-provenance",
            str(REFERENCE_PROVENANCE),
            "--c",
            "100",
            "--N",
            "200",
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    assert result.stdout.strip() == (
        "dimensionally consistent Groskin provenance metadata: true"
    )


def test_quadratic_form_uses_exact_fraction_arithmetic():
    matrix = weil.fraction_matrix([["2", "1/3"], ["1/3", "5/2"]])
    vector = (Fraction(2, 3), Fraction(-3, 5))

    value = weil.quadratic_form(matrix, vector)

    assert value == Fraction(137, 90)
    assert isinstance(value, Fraction)


def test_fraction_matrix_rejects_nonsymmetric_input():
    with pytest.raises(ValueError, match="symmetric"):
        weil.fraction_matrix([[1, 2], [3, 4]])


def test_exact_ldlt_certificate_for_positive_definite_matrix():
    matrix = weil.fraction_matrix([[4, 2], [2, 3]])

    certificate = weil.ldlt_decompose(matrix)

    assert certificate.lower == (
        (Fraction(1), Fraction(0)),
        (Fraction(1, 2), Fraction(1)),
    )
    assert certificate.diagonal == (Fraction(4), Fraction(2))
    assert weil.verify_ldlt_certificate(matrix, certificate)


def test_exact_ldlt_certificate_accepts_singular_psd_matrix():
    matrix = weil.fraction_matrix([[1, 1], [1, 1]])

    certificate = weil.ldlt_decompose(matrix)

    assert certificate.diagonal == (Fraction(1), Fraction(0))
    assert weil.verify_ldlt_certificate(matrix, certificate)


def test_exact_ldlt_certificate_accepts_leading_zero_pivot():
    matrix = weil.fraction_matrix([[0, 0, 0], [0, 2, 1], [0, 1, 3]])

    certificate = weil.ldlt_decompose(matrix)

    assert certificate.diagonal == (Fraction(0), Fraction(2), Fraction(5, 2))
    assert weil.verify_ldlt_certificate(matrix, certificate)


def test_exact_ldlt_certificate_accepts_interior_zero_pivot():
    matrix = weil.fraction_matrix(
        [[2, 1, -2], [1, "1/2", -1], [-2, -1, 5]]
    )

    certificate = weil.ldlt_decompose(matrix)

    assert certificate.diagonal == (Fraction(2), Fraction(0), Fraction(3))
    assert certificate.lower[2][1] == 0
    assert weil.verify_ldlt_certificate(matrix, certificate)


def test_indefinite_factorization_is_not_a_psd_certificate():
    matrix = weil.fraction_matrix([[1, 2], [2, 1]])

    certificate = weil.ldlt_decompose(matrix)

    assert certificate.diagonal == (Fraction(1), Fraction(-3))
    assert weil.verify_ldlt_certificate(
        matrix, certificate, require_nonnegative=False
    )
    assert not weil.verify_ldlt_certificate(matrix, certificate)


def test_zero_pivot_with_nonzero_residual_is_rejected():
    matrix = weil.fraction_matrix([[0, 1], [1, 0]])

    with pytest.raises(weil.LDLDecompositionError, match="zero pivot"):
        weil.ldlt_decompose(matrix)


def test_tampered_ldlt_certificate_fails_exact_check():
    matrix = weil.fraction_matrix([[4, 2], [2, 3]])
    certificate = weil.ldlt_decompose(matrix)
    tampered = weil.LDLCertificate(
        lower=certificate.lower,
        diagonal=(certificate.diagonal[0], Fraction(3)),
    )

    assert not weil.verify_ldlt_certificate(matrix, tampered)


def test_interval_certificate_proves_positive_definiteness_from_center_radius():
    enclosure = weil.interval_matrix_from_center_radius(
        [[4, 2], [2, 3]],
        [["1/10", "1/10"], ["1/10", "1/10"]],
    )

    certificate = weil.certify_interval_matrix(enclosure)

    assert certificate.center_lower_bound == Fraction(8, 9)
    assert certificate.perturbation_row_bound == Fraction(1, 5)
    assert weil.verify_interval_matrix_certificate(
        enclosure, certificate, require_positive=True
    )


def test_lower_upper_and_center_radius_define_the_same_enclosure():
    from_bounds = weil.interval_matrix_from_bounds(
        [["39/10", "19/10"], ["19/10", "29/10"]],
        [["41/10", "21/10"], ["21/10", "31/10"]],
    )
    from_center_radius = weil.interval_matrix_from_center_radius(
        [[4, 2], [2, 3]],
        [["1/10", "1/10"], ["1/10", "1/10"]],
    )

    assert from_bounds == from_center_radius


def test_interval_certificate_distinguishes_psd_boundary_from_pd():
    enclosure = weil.interval_matrix_from_center_radius(
        [[4, 2], [2, 3]],
        [["4/9", "4/9"], ["4/9", "4/9"]],
    )
    certificate = weil.certify_interval_matrix(enclosure)

    assert certificate.center_lower_bound == Fraction(8, 9)
    assert certificate.perturbation_row_bound == Fraction(8, 9)
    assert weil.verify_interval_matrix_certificate(enclosure, certificate)
    assert not weil.verify_interval_matrix_certificate(
        enclosure, certificate, require_positive=True
    )


@pytest.mark.parametrize(
    ("center", "radius", "message"),
    [
        ([[1, 0], [0, 1]], [[0, 0]], "same shape"),
        ([[1, 2], [0, 1]], [[0, 0], [0, 0]], "center.*symmetric"),
        ([[1, 0], [0, 1]], [[0, 1], [0, 0]], "radius.*symmetric"),
        ([[1, 0], [0, 1]], [[0, 0], [0, -1]], "nonnegative"),
    ],
)
def test_center_radius_interval_validation_is_strict(center, radius, message):
    with pytest.raises(ValueError, match=message):
        weil.interval_matrix_from_center_radius(center, radius)


@pytest.mark.parametrize(
    ("lower", "upper", "message"),
    [
        ([[0, 0], [0, 0]], [[1, 0]], "same shape"),
        ([[0, 1], [0, 0]], [[1, 1], [1, 1]], "lower.*symmetric"),
        ([[0, 0], [0, 0]], [[1, 1], [0, 1]], "upper.*symmetric"),
        ([[0, 0], [0, 2]], [[1, 0], [0, 1]], "lower.*upper"),
    ],
)
def test_lower_upper_interval_validation_is_strict(lower, upper, message):
    with pytest.raises(ValueError, match=message):
        weil.interval_matrix_from_bounds(lower, upper)


def test_interval_certificate_rejects_center_without_positive_ldlt_pivots():
    enclosure = weil.interval_matrix_from_center_radius(
        [[1, 2], [2, 1]], [[0, 0], [0, 0]]
    )

    with pytest.raises(ValueError, match="strictly positive"):
        weil.certify_interval_matrix(enclosure)


def test_interval_certificate_rejects_budget_that_exhausts_center_margin():
    enclosure = weil.interval_matrix_from_center_radius(
        [[4, 2], [2, 3]],
        [["1/2", "1/2"], ["1/2", "1/2"]],
    )
    certificate = weil.certify_interval_matrix(enclosure)

    assert certificate.perturbation_row_bound == 1
    assert not weil.verify_interval_matrix_certificate(enclosure, certificate)


def test_interval_certificate_recomputes_tampered_margin_and_inverse():
    enclosure = weil.interval_matrix_from_center_radius(
        [[4, 2], [2, 3]],
        [["1/10", "1/10"], ["1/10", "1/10"]],
    )
    certificate = weil.certify_interval_matrix(enclosure)
    tampered_margin = weil.IntervalMatrixCertificate(
        ldlt=certificate.ldlt,
        inverse_transpose=certificate.inverse_transpose,
        center_lower_bound=certificate.center_lower_bound + 1,
        perturbation_row_bound=certificate.perturbation_row_bound,
    )
    tampered_inverse = weil.IntervalMatrixCertificate(
        ldlt=certificate.ldlt,
        inverse_transpose=((Fraction(1), Fraction(0)), (Fraction(0), Fraction(1))),
        center_lower_bound=certificate.center_lower_bound,
        perturbation_row_bound=certificate.perturbation_row_bound,
    )

    assert not weil.verify_interval_matrix_certificate(enclosure, tampered_margin)
    assert not weil.verify_interval_matrix_certificate(enclosure, tampered_inverse)


def test_experiment_artifact_round_trip_is_canonical_and_self_checking(tmp_path):
    matrix = weil.fraction_matrix([[4, 2], [2, 3]])
    certificate = weil.ldlt_decompose(matrix)
    output = tmp_path / "certificate.json"

    record = weil.write_experiment_artifact(
        output,
        matrix,
        certificate,
        parameters={"c": 100, "N": 1, "sector": "prototype"},
    )
    loaded = weil.load_experiment_artifact(output)

    expected_bytes = (
        json.dumps(
            record,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")
    assert output.read_bytes() == expected_bytes
    assert json.loads(output.read_text()) == record
    assert loaded["schema_version"] == "weil-extremal-kernel-ldlt/v1"
    assert loaded["claim_scope"] == "finite-rational-matrix-only"
    assert loaded["matrix"] == [["4", "2"], ["2", "3"]]
    assert loaded["certificate"]["lower"][1][0] == "1/2"
    assert loaded["result"] == {
        "certified_psd": True,
        "exact_reconstruction": True,
        "nonnegative_diagonal": True,
    }
    assert weil.verify_experiment_artifact(loaded)
    assert weil.verify_experiment_artifact_file(output)


@pytest.mark.parametrize("encoding", ["pretty", "missing-newline"])
def test_experiment_artifact_replay_rejects_noncanonical_bytes(tmp_path, encoding):
    matrix = weil.fraction_matrix([[4, 2], [2, 3]])
    output = tmp_path / "certificate.json"
    record = weil.write_experiment_artifact(
        output,
        matrix,
        weil.ldlt_decompose(matrix),
        parameters={"c": 100, "N": 1},
    )
    if encoding == "pretty":
        output.write_text(
            json.dumps(record, sort_keys=True, indent=2, allow_nan=False) + "\n",
            encoding="utf-8",
        )
    else:
        output.write_bytes(output.read_bytes()[:-1])

    assert not weil.verify_experiment_artifact_file(output)
    replay = subprocess.run(
        [
            sys.executable,
            "-m",
            "experiments.rh.weil_extremal_kernels",
            "verify",
            str(output),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert replay.returncode == 1
    assert replay.stdout.strip() == "valid exact LDL^T artifact: false"


def test_experiment_artifact_rejects_nan_on_write_and_replay(tmp_path):
    matrix = weil.fraction_matrix([[4, 2], [2, 3]])
    certificate = weil.ldlt_decompose(matrix)
    output = tmp_path / "certificate.json"

    with pytest.raises(ValueError, match="JSON compliant"):
        weil.write_experiment_artifact(
            output,
            matrix,
            certificate,
            parameters={"bad": float("nan")},
        )

    output.write_bytes(b'{"parameters":{"bad":NaN}}\n')
    with pytest.raises(ValueError, match="non-finite JSON constant"):
        weil.load_experiment_artifact(output)
    assert not weil.verify_experiment_artifact_file(output)


def test_experiment_artifact_rejects_tampering(tmp_path):
    matrix = weil.fraction_matrix([[4, 2], [2, 3]])
    output = tmp_path / "certificate.json"
    record = weil.write_experiment_artifact(
        output,
        matrix,
        weil.ldlt_decompose(matrix),
        parameters={"c": 100, "N": 1},
    )
    record["matrix"][0][0] = "5"

    assert not weil.verify_experiment_artifact(record)


@pytest.mark.parametrize(
    "key",
    ["certified_psd", "exact_reconstruction", "nonnegative_diagonal"],
)
@pytest.mark.parametrize("replacement", [0, 1])
def test_experiment_artifact_result_requires_actual_booleans(
    tmp_path, key, replacement
):
    matrix = weil.fraction_matrix([[4, 2], [2, 3]])
    output = tmp_path / "certificate.json"
    record = weil.write_experiment_artifact(
        output,
        matrix,
        weil.ldlt_decompose(matrix),
        parameters={"c": 100, "N": 1},
    )
    record["result"][key] = replacement
    refresh_payload_digest(record)

    assert not weil.verify_experiment_artifact(record)


def test_experiment_artifact_result_rejects_extra_keys(tmp_path):
    matrix = weil.fraction_matrix([[4, 2], [2, 3]])
    output = tmp_path / "certificate.json"
    record = weil.write_experiment_artifact(
        output,
        matrix,
        weil.ldlt_decompose(matrix),
        parameters={"c": 100, "N": 1},
    )
    record["result"]["unexpected"] = False
    refresh_payload_digest(record)

    assert not weil.verify_experiment_artifact(record)


def test_interval_artifact_round_trip_replays_enclosure_certificate(tmp_path):
    enclosure = weil.interval_matrix_from_center_radius(
        [[4, 2], [2, 3]],
        [["1/10", "1/10"], ["1/10", "1/10"]],
    )
    certificate = weil.certify_interval_matrix(enclosure)
    output = tmp_path / "interval-certificate.json"

    record = weil.write_interval_experiment_artifact(
        output,
        enclosure,
        certificate,
        parameters={"c": 100, "N": 1, "assembly": "test-fixture"},
    )

    assert record["schema_version"] == "weil-extremal-kernel-interval-ldlt/v1"
    assert record["claim_scope"] == "finite-rational-interval-matrix-only"
    assert record["enclosure"]["lower"] == [
        ["39/10", "19/10"],
        ["19/10", "29/10"],
    ]
    assert record["certificate"]["inverse_transpose"] == [
        ["1", "-1/2"],
        ["0", "1"],
    ]
    assert record["result"] == {
        "center_lower_bound": "8/9",
        "certified_pd": True,
        "certified_psd": True,
        "exact_center_reconstruction": True,
        "inverse_transpose_identity": True,
        "perturbation_row_bound": "1/5",
        "positive_diagonal": True,
    }
    assert weil.verify_interval_experiment_artifact(record)
    assert weil.verify_interval_experiment_artifact_file(output)


@pytest.mark.parametrize(
    ("path", "replacement"),
    [
        (("certificate", "diagonal", 1), "3"),
        (("certificate", "inverse_transpose", 0, 1), "0"),
        (("result", "center_lower_bound"), "100"),
        (("result", "certified_pd"), 1),
        (("enclosure", "upper", 0, 1), "100"),
    ],
)
def test_interval_artifact_rejects_rehashed_adversarial_tampering(
    tmp_path, path, replacement
):
    enclosure = weil.interval_matrix_from_center_radius(
        [[4, 2], [2, 3]],
        [["1/10", "1/10"], ["1/10", "1/10"]],
    )
    output = tmp_path / "interval-certificate.json"
    record = weil.write_interval_experiment_artifact(
        output,
        enclosure,
        weil.certify_interval_matrix(enclosure),
        parameters={"c": 100, "N": 1},
    )
    target = record
    for key in path[:-1]:
        target = target[key]
    target[path[-1]] = replacement
    refresh_payload_digest(record)

    assert not weil.verify_interval_experiment_artifact(record)


def test_cli_certifies_and_replays_center_radius_interval(tmp_path):
    input_path = tmp_path / "interval.json"
    output_path = tmp_path / "interval-certificate.json"
    input_path.write_text(
        json.dumps(
            {
                "center": [["4", "2"], ["2", "3"]],
                "radius": [["1/10", "1/10"], ["1/10", "1/10"]],
                "parameters": {"c": 100, "N": 1},
            }
        )
        + "\n",
        encoding="utf-8",
    )

    certify = subprocess.run(
        [
            sys.executable,
            "-m",
            "experiments.rh.weil_extremal_kernels",
            "certify-interval",
            str(input_path),
            str(output_path),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    verify = subprocess.run(
        [
            sys.executable,
            "-m",
            "experiments.rh.weil_extremal_kernels",
            "verify-interval",
            str(output_path),
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    assert certify.stdout.strip() == "certified interval matrix positive definite: true"
    assert verify.stdout.strip() == "valid interval LDL^T artifact: true"


def test_cli_certify_and_verify_round_trip(tmp_path):
    input_path = tmp_path / "matrix.json"
    output_path = tmp_path / "certificate.json"
    input_path.write_text(
        json.dumps(
            {
                "matrix": [["4", "2"], ["2", "3"]],
                "parameters": {"c": 100, "N": 1, "sector": "prototype"},
            }
        )
        + "\n",
        encoding="utf-8",
    )

    certify = subprocess.run(
        [
            sys.executable,
            "-m",
            "experiments.rh.weil_extremal_kernels",
            "certify",
            str(input_path),
            str(output_path),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    verify = subprocess.run(
        [
            sys.executable,
            "-m",
            "experiments.rh.weil_extremal_kernels",
            "verify",
            str(output_path),
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    assert certify.stdout.strip() == "certified finite rational matrix: true"
    assert verify.stdout.strip() == "valid exact LDL^T artifact: true"
