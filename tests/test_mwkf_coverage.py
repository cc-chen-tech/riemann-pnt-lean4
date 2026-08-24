from fractions import Fraction as F
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.audit_mwkf_coverage import (
    TARGET_SAVING,
    bcr_adapter,
    completion_dual_exponent,
    h_completion_adapter,
    h_poisson_shifted_scales,
    h_poisson_subbox_scales,
    route_box,
    wright_fixed_factor_adapter,
)
from scripts.audit_mwkf_ranges import ExponentBox, boundary_witnesses


COVERAGE_NOTE = Path(
    "docs/research/2026-08-24-mwkf-published-coverage.md"
)


def test_bcr_covers_a_small_third_variable_box() -> None:
    box = ExponentBox(F(1), F(1), F(0), F(0), F(0), F(0), F(2))
    result = bcr_adapter(box)
    assert result.applicable
    assert result.route == "bcr"
    assert result.saving == F(1, 20)
    assert result.saving >= TARGET_SAVING


def test_balanced_maximal_box_has_exact_bcr_deficit() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    result = bcr_adapter(box)
    assert not result.applicable
    assert result.saving == F(-37, 8)
    assert result.reason == "insufficient_saving"


def test_short_h_poisson_has_half_power_dual_not_a_kinematic_rejection() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert completion_dual_exponent(box.h, box.sigma) == F(1, 2)
    result = h_completion_adapter(box)
    assert not result.applicable
    assert result.reason == "no_cited_completed_kernel_bound"
    assert "dual exponent max(0,sigma-h)=1/2" in result.conditions


def test_balanced_h_poisson_reduces_to_exact_critical_shifted_scales() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    scales = h_poisson_shifted_scales(box)
    assert scales.v == F(1, 2)
    assert scales.j == F(1, 2)
    assert scales.shift == F(5, 2)
    assert scales.target == F(7, 2)
    assert scales.gate_target == F(3499, 1000)
    assert scales.volume == F(6)
    assert scales.required_saving == F(2501, 1000)
    assert scales.square_root_margin == F(499, 1000)


def test_v_equals_j_equals_one_is_an_exact_average_chowla_witness() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    scales = h_poisson_subbox_scales(box, v=F(0), j=F(0))
    assert scales.volume == F(11, 2)
    assert scales.target == F(7, 2)
    assert scales.gate_target == F(3499, 1000)
    assert scales.required_saving == F(2001, 1000)
    assert scales.square_root_margin == F(749, 1000)


def test_wright_rejects_a_box_without_a_fixed_denominator_factor() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    result = wright_fixed_factor_adapter(box, fixed_factor=None)
    assert not result.applicable
    assert result.reason == "no_fixed_denominator_factor"


def test_primary_route_is_unique_and_residual_is_explicit() -> None:
    small = ExponentBox(F(1), F(1), F(0), F(0), F(0), F(0), F(2))
    assert route_box(small).route == "bcr"

    balanced = boundary_witnesses()["balanced_max_a"]
    residual = route_box(balanced)
    assert residual.route == "mobius_type_i_ii"
    assert residual.reason == "published_routes_exhausted"
    assert residual.saving is None


def test_coverage_note_has_hypothesis_and_residual_ledgers() -> None:
    text = COVERAGE_NOTE.read_text()
    for marker in (
        "## 2. Exact BCR adapter",
        "## 3. Completion adapters",
        r"v=k s+\delta\bar r",
        r"\delta=rv-js",
        r"\mathrm{SM}_{1/1000}",
        r"T^{7/2-1/1000}",
        r"\mathrm{RES}_{1,1}",
        r"T^{11/2}",
        r"T^{2+1/1000}",
        "## 4. Wright fixed-factor adapter",
        "## 5. Exact residual witnesses",
        "published coverage result: residual cells remain",
    ):
        assert marker in text
    assert "-37/8" in text
    assert "no_fixed_denominator_factor" in text
