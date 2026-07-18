import hashlib
import json
import subprocess
import sys
from fractions import Fraction

import pytest

from experiments.rh import weil_extremal_kernels as weil


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
