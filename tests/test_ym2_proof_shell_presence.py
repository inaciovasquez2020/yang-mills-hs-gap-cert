from pathlib import Path

def test_ym2_proof_shell_present() -> None:
    p = Path("proofs/YM2/GAUGE_INVARIANT_COERCIVITY_PROOF_SHELL.md")
    text = p.read_text()
    assert "## Status" in text
    assert "OPEN" in text
    assert "physical quotient" in text
    assert "Blocking lemma" in text
