from pathlib import Path

def test_ym3_next_missing_object_2026_04() -> None:
    s = Path("docs/status/YM3_NEXT_MISSING_OBJECT_2026_04.md").read_text()
    shell = Path("proofs/YM3/REFLECTION_POSITIVITY_BRIDGE_PROOF_SHELL.md").read_text()
    missing = Path("proofs/gap/MISSING_YANG_MILLS_INGREDIENTS.md").read_text()
    assert "Status: OPEN" in s
    assert "Yang-Mills reflection positivity or transfer-matrix argument" in s
    assert "REFLECTION_POSITIVITY_SURVIVES_BLOCKING" in s
    assert "# YM-3 — Reflection positivity bridge" in shell
    assert "YM-3: Reflection positivity bridge" in missing
