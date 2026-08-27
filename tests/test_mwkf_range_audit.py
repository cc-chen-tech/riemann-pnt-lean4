from fractions import Fraction as F
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.audit_mwkf_ranges import (
    ExponentBox,
    admissible_polytope_strict_interior_witness,
    admissible_polytope_vertices,
    admissibility_violations,
    boundary_witnesses,
    derived_bounds,
    is_admissible,
)


NOTE = Path("docs/research/2026-08-24-mobius-weighted-off-diagonal.md")


def test_balanced_maximal_third_variable_box() -> None:
    box = ExponentBox(
        rho=F(3), sigma=F(3), m=F(1, 2), k=F(1, 2),
        ell=F(5, 2), h=F(5, 2), kappa=F(0),
    )
    assert box.third_length == F(5)
    assert admissibility_violations(box) == ()
    assert is_admissible(box)


def test_unbalanced_endpoint_boxes_remain_admissible() -> None:
    witnesses = boundary_witnesses()
    assert set(witnesses) == {
        "balanced_max_a", "r_long", "s_long", "large_q_endpoint"
    }
    assert all(is_admissible(box) for box in witnesses.values())
    assert witnesses["r_long"].third_length == F(4)
    assert witnesses["s_long"].third_length == F(4)
    assert witnesses["large_q_endpoint"].kappa == F(2)


def test_derived_bounds_match_the_written_polytope() -> None:
    for box in boundary_witnesses().values():
        bounds = derived_bounds(box)
        assert bounds["a"] == box.ell + box.h
        assert bounds["a"] <= bounds["a_cap"]
        assert box.m <= bounds["m_cap"]
        assert box.k <= bounds["k_cap"]


def test_balanced_box_exhibits_the_long_a_gap() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert box.third_length == F(5)
    assert (box.rho + box.sigma) / 2 == F(3)
    assert box.third_length - (box.rho + box.sigma) / 2 == F(2)


def test_exact_admissible_polytope_has_25_vertices() -> None:
    vertices = admissible_polytope_vertices()
    assert len(vertices) == 25
    assert len(set(vertices)) == 25
    assert all(is_admissible(box) for box in vertices)


def test_reduced_polytope_is_full_dimensional() -> None:
    box = admissible_polytope_strict_interior_witness()
    assert is_admissible(box)
    assert min(
        box.rho, box.sigma, box.m, box.k,
        box.ell, box.h, box.kappa,
    ) > 0
    assert box.kappa + box.rho < 3
    assert box.kappa + box.sigma < 3
    assert box.k + box.m < 1
    assert box.ell < box.m + box.rho - 1
    assert box.h < box.sigma - box.m
    assert box.third_length < box.rho + box.sigma - 1


def test_exact_vertex_ledger_contains_every_named_boundary_witness() -> None:
    vertices = set(admissible_polytope_vertices())
    assert set(boundary_witnesses().values()) <= vertices


def test_exact_vertex_ledger_is_stable() -> None:
    vertices = admissible_polytope_vertices()
    tuples = [
        (box.rho, box.sigma, box.m, box.k,
         box.ell, box.h, box.kappa)
        for box in vertices
    ]
    assert tuples == [
        (F(0), F(1), F(1), F(0), F(0), F(0), F(0)),
        (F(0), F(1), F(1), F(0), F(0), F(0), F(2)),
        (F(1, 2), F(1, 2), F(1, 2), F(1, 2), F(0), F(0), F(5, 2)),
        (F(1), F(0), F(0), F(1), F(0), F(0), F(0)),
        (F(1), F(0), F(0), F(1), F(0), F(0), F(2)),
        (F(1), F(1), F(0), F(0), F(0), F(0), F(0)),
        (F(1), F(1), F(0), F(0), F(0), F(0), F(2)),
        (F(1), F(1), F(0), F(0), F(0), F(1), F(0)),
        (F(1), F(1), F(0), F(0), F(0), F(1), F(2)),
        (F(2), F(3), F(1), F(0), F(0), F(0), F(0)),
        (F(2), F(3), F(1), F(0), F(0), F(2), F(0)),
        (F(2), F(3), F(1), F(0), F(2), F(0), F(0)),
        (F(2), F(3), F(1), F(0), F(2), F(2), F(0)),
        (F(3), F(2), F(0), F(1), F(0), F(0), F(0)),
        (F(3), F(2), F(0), F(1), F(0), F(2), F(0)),
        (F(3), F(2), F(0), F(1), F(2), F(0), F(0)),
        (F(3), F(2), F(0), F(1), F(2), F(2), F(0)),
        (F(3), F(3), F(0), F(0), F(0), F(0), F(0)),
        (F(3), F(3), F(0), F(0), F(0), F(3), F(0)),
        (F(3), F(3), F(0), F(0), F(2), F(0), F(0)),
        (F(3), F(3), F(0), F(0), F(2), F(3), F(0)),
        (F(3), F(3), F(1, 2), F(1, 2), F(0), F(0), F(0)),
        (F(3), F(3), F(1, 2), F(1, 2), F(0), F(5, 2), F(0)),
        (F(3), F(3), F(1, 2), F(1, 2), F(5, 2), F(0), F(0)),
        (F(3), F(3), F(1, 2), F(1, 2), F(5, 2), F(5, 2), F(0)),
    ]


@pytest.mark.parametrize(
    ("box", "code"),
    [
        (ExponentBox(F(-1), F(1), F(0), F(0), F(0), F(0), F(0)),
         "nonnegative"),
        (ExponentBox(F(3), F(1), F(0), F(2), F(0), F(0), F(1)),
         "mollifier_r"),
        (ExponentBox(F(1), F(3), F(2), F(0), F(0), F(0), F(1)),
         "mollifier_s"),
        (ExponentBox(F(2), F(2), F(1), F(1), F(0), F(0), F(0)),
         "km_length"),
        (ExponentBox(F(2), F(2), F(0), F(1), F(0), F(0), F(0)),
         "ratio_balance"),
        (ExponentBox(F(2), F(2), F(0), F(0), F(2), F(0), F(0)),
         "delta_length"),
        (ExponentBox(F(2), F(2), F(0), F(0), F(0), F(3), F(0)),
         "frequency_length"),
        (ExponentBox(F(2), F(2), F(0), F(0), F(0), F(4), F(0)),
         "third_length"),
    ],
)
def test_each_constraint_has_a_stable_failure_code(
    box: ExponentBox, code: str
) -> None:
    assert code in admissibility_violations(box)
    assert not is_admissible(box)


def test_research_note_exposes_afe_audit_ledger() -> None:
    text = NOTE.read_text()
    for marker in (
        "> **Current proof status.**",
        "### 2.1 Completion and pole cancellation",
        "### 2.2 Absolute convergence and termwise expansion",
        "### 2.3 Uniform weight bounds",
    ):
        assert marker in text
    assert "\\Lambda(s)=\\gamma(s)\\zeta(s)" in text
    assert "\\left(1-4z^2\\right)" in text


def test_research_note_exposes_poisson_audit_ledger() -> None:
    text = NOTE.read_text()
    for marker in (
        "### 4.1 Residue class and Poisson normalization",
        "### 4.2 Zero mode from a common Mellin integral",
        "### 4.3 Residue and main-term normalization",
    ):
        assert marker in text
    assert "zero-mode audit result:" in text
    assert "C_t(z)\\zeta(1-2z)g_t(-z)" in text
    assert "\\mathcal E_{\\rm arch}" in text


def test_research_note_has_one_honest_phase_one_classification() -> None:
    text = NOTE.read_text()
    labels = (
        "Phase-1 classification: exact reduction verified",
        "Phase-1 classification: corrected reduction verified",
        "Phase-1 classification: exact reduction remains blocked",
    )
    assert sum(label in text for label in labels) == 1
    assert "Accepted local gate after exact audit:" in text
    assert "arXiv:2601.00292" in text
    assert "withdrawn" in text.lower()
