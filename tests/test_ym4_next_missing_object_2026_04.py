from pathlib import Path

def test_ym4_next_missing_object_2026_04() -> None:
    s = Path("docs/status/YM4_NEXT_MISSING_OBJECT_2026_04.md").read_text()
    shell = Path("proofs/YM4/CONTINUUM_TRANSFER_PROOF_SHELL.md").read_text()
    missing = Path("proofs/gap/MISSING_YANG_MILLS_INGREDIENTS.md").read_text()
    assert "Status: OPEN" in s
    assert "lattice lower bound survives the continuum and infinite-volume limit" in s
    assert "Lower-semicontinuity / stability transfer statement." in s
    assert "# YM-4 — Continuum transfer" in shell
    assert "YM-4: Continuum transfer" in missing
