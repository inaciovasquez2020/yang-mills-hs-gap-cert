from pathlib import Path

def test_ym5_next_missing_object_2026_04() -> None:
    s = Path("docs/status/YM5_NEXT_MISSING_OBJECT_2026_04.md").read_text()
    shell = Path("proofs/YM5/MASS_GAP_OBSERVABLE_PROOF_SHELL.md").read_text()
    missing = Path("proofs/gap/MISSING_YANG_MILLS_INGREDIENTS.md").read_text()
    assert "Status: OPEN" in s
    assert "gauge-invariant correlator/observable whose decay is forced by the coercive lower bound" in s
    assert "Observable-level mass-gap conclusion." in s
    assert "# YM-5 — Mass-gap observable" in shell
    assert "YM-5: Mass-gap observable" in missing
