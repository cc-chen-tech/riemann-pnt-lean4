"""Integration gate for certificate-chain links 1/2 at small N.

Regenerates the dual-route interval merge for the frozen small-N cases
(c=13, N=4 and N=8) and asserts:

1. entrywise overlap between the two independent interval assembly routes
   is non-empty everywhere (no OverlapError);
2. the merged, symmetrized intervals are consistent with both routes' frozen
   high-precision audit point values from
   groskin_2607_02828_v1_small_n_high_precision_crosscheck.json, up to that
   artifact's own numerical_tolerance (1e-60).

Note (verified 2026-07-22 by recomputing entry (-8,-8) of the N=8 case at
200 dps with both assembly routes): the frozen artifact's
`ccm_hypergeometric_lerch_high_precision_audit` prints are only accurate to
~71 digits despite the advertised 130 audit digits (they deviate 3.7e-71 from
the 200-dps value, while the auxiliary audits agree to 3.6e-121). The
interval artifacts produced by this branch are sound — the merged intervals
do contain the 200-dps truth — so literal containment against the frozen CCM
audit print is too strong a gate. The correct gate is distance-to-interval
bounded by the frozen artifact's own numerical_tolerance.
3. symmetrization actually happened (entry (i,j) == entry (j,i));
4. the shipped merged artifacts match the regenerated merge.

This is the rigorous-interval successor of the pointwise crosscheck; it
still does not close Gate A (registered target is c=100, N=200).
"""

import json
from decimal import Decimal
from pathlib import Path

import pytest

from experiments.rh import weil_extremal_interval_overlap as ov

ROOT = Path(__file__).resolve().parent.parent
REF = ROOT / "experiments" / "rh" / "reference"

CASES = [(13, 4), (13, 8)]

AUX = "weil_extremal_interval_auxiliary_closed_form_interval_arb_c{c}_N{n}_prec256.json"
CCM = "weil_extremal_interval_assembly_ccm_hypergeometric_lerch_c{c}_N{n}_prec256.json"
MERGED = "weil_extremal_interval_overlap_c{c}_N{n}_prec256.json"
FROZEN = "groskin_2607_02828_v1_small_n_high_precision_crosscheck.json"


def _load(name):
    return json.loads((REF / name).read_text())


def _frozen_case(c, n):
    frozen = _load(FROZEN)
    for case in frozen["cases"]:
        if case["c"] == c and case["N"] == n:
            return case
    raise AssertionError(f"no frozen case for c={c}, N={n}")


@pytest.mark.parametrize("c,n", CASES)
def test_dual_route_merge_contains_frozen_audit_values(c, n):
    aux = _load(AUX.format(c=c, n=n))
    ccm = _load(CCM.format(c=c, n=n))
    merged = ov.merge_artifacts(aux, ccm)  # raises OverlapError on empty intersection
    case = _frozen_case(c, n)
    tolerance = Decimal(case["numerical_tolerance"])
    dim = merged["dimension"]
    assert len(merged["entries"]) == dim * dim == case["entry_count"]
    worst = Decimal(0)
    violations = []
    for idx, (lo, hi) in enumerate(merged["entries"]):
        lo_d, hi_d = Decimal(lo), Decimal(hi)
        for field in (
            "auxiliary_closed_form_high_precision_audit",
            "ccm_hypergeometric_lerch_high_precision_audit",
        ):
            value = Decimal(case["entries"][idx][field])
            distance = max(lo_d - value, value - hi_d, Decimal(0))
            worst = max(worst, distance)
            if distance > tolerance:
                violations.append((idx, field, str(distance)))
    assert violations == []
    # Sanity: consistency is much better than the frozen tolerance demands.
    assert worst < tolerance


@pytest.mark.parametrize("c,n", CASES)
def test_merged_artifact_is_symmetric(c, n):
    merged = ov.merge_artifacts(_load(AUX.format(c=c, n=n)), _load(CCM.format(c=c, n=n)))
    dim = merged["dimension"]
    entries = merged["entries"]
    for i in range(dim):
        for j in range(i + 1, dim):
            assert entries[i * dim + j] == entries[j * dim + i]


@pytest.mark.parametrize("c,n", CASES)
def test_shipped_merged_artifact_matches_regeneration(c, n):
    shipped = _load(MERGED.format(c=c, n=n))
    regenerated = ov.merge_artifacts(_load(AUX.format(c=c, n=n)), _load(CCM.format(c=c, n=n)))
    assert shipped["entries"] == regenerated["entries"]
    ov.validate_artifact(shipped)
