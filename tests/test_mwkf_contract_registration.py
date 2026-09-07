"""Keep the cubic-MWKF contracts in the default Lean build, not just on disk."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]


def test_all_cubic_mwkf_and_mellin_contracts_are_default_roots():
    lakefile = (ROOT / "lakefile.lean").read_text()
    roots = set(re.findall(r"`([A-Za-z0-9_.]+)\s*,", lakefile))
    contracts = sorted((ROOT / "Test").glob("MWKFCubic*.lean"))
    contracts += sorted((ROOT / "Test").glob("MellinVerticalStripBound*.lean"))
    assert len(contracts) >= 138
    expected = {"Test." + path.stem for path in contracts}
    assert not expected - roots, sorted(expected - roots)


def test_ci_installs_the_python_test_dependencies():
    workflow = (ROOT / ".github" / "workflows" / "lean-ci.yml").read_text()
    install = "python3 -m pip install pytest numpy python-flint mpmath scipy"
    assert install in workflow
    assert workflow.index(install) < workflow.index("python3 -m pytest")
