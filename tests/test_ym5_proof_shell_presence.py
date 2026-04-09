from pathlib import Path

def test_ym5_proof_shell_present() -> None:
    p = Path("proofs/YM5/MASS_GAP_OBSERVABLE_PROOF_SHELL.md")
    text = p.read_text()
    assert "## Status" in text
    assert "OPEN" in text
    assert "gauge-invariant observable" in text
    assert "Blocking lemma" in text
