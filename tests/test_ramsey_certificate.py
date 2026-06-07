import json
import subprocess
import sys

from experiments.discrete import ramsey_search as ramsey


def test_export_and_load_certificate_round_trip(tmp_path):
    graph = ramsey.find_counterexample(5, clique_size=3, independent_size=3)
    certificate_path = tmp_path / "ramsey_r3_3_n5.json"

    assert graph is not None
    certificate = ramsey.export_certificate(graph, 3, 3, certificate_path)
    loaded = ramsey.load_certificate(certificate_path)

    assert certificate == loaded
    assert set(loaded) == {
        "vertices",
        "edges",
        "clique_size",
        "independent_size",
        "has_clique",
        "has_independent_set",
        "is_counterexample",
    }
    assert loaded["vertices"] == 5
    assert loaded["clique_size"] == 3
    assert loaded["independent_size"] == 3
    assert loaded["has_clique"] is False
    assert loaded["has_independent_set"] is False
    assert loaded["is_counterexample"] is True
    assert ramsey.verify_certificate(loaded)


def test_tampered_certificate_fails_verification(tmp_path):
    graph = ramsey.find_counterexample(5, clique_size=3, independent_size=3)
    certificate_path = tmp_path / "ramsey_r3_3_n5.json"

    assert graph is not None
    certificate = ramsey.export_certificate(graph, 3, 3, certificate_path)
    certificate["has_clique"] = True
    certificate_path.write_text(json.dumps(certificate), encoding="utf-8")

    assert not ramsey.verify_certificate(ramsey.load_certificate(certificate_path))


def test_cli_keeps_graph_output_and_writes_certificate(tmp_path):
    certificate_path = tmp_path / "ramsey_r3_3_n5.json"

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "experiments.discrete.ramsey_search",
            "--vertices",
            "5",
            "--clique-size",
            "3",
            "--independent-size",
            "3",
            "--certificate-output",
            str(certificate_path),
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    assert result.stdout.strip()
    assert ramsey.verify_certificate(ramsey.load_certificate(certificate_path))
