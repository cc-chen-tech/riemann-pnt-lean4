from pathlib import Path


def test_global_gate_does_not_revert_to_fixed_entry_pevp_only():
    text = Path("docs/research/2026-08-24-mobius-weighted-off-diagonal.md").read_text()
    gate = text.split("Accepted local gate after exact audit: coupled-kernel.", 1)[1]
    gate = gate.split("### 6.2 Boundary diagnostics", 1)[0]
    assert "This gate is unproved." in gate
    assert "It too is unproved;" in gate
    assert "reduces it to PEVP" not in gate
    assert "seminorm-stable PEVP estimate, shell by shell" not in gate
