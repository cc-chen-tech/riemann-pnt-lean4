from fractions import Fraction as F
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.audit_mwkf_ranges import (
    ExponentBox,
    admissibility_violations,
    boundary_witnesses,
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


def test_research_note_exposes_poisson_audit_ledger() -> None:
    text = NOTE.read_text()
    for marker in (
        "### 4.1 Residue class and Poisson normalization",
        "### 4.2 Zero mode from a common Mellin integral",
        "### 4.3 Residue and main-term normalization",
    ):
        assert marker in text
    assert "zero-mode audit result:" in text
