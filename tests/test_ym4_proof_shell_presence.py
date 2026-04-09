from pathlib import Path

def test_ym4_proof_shell_present() -> None:
    p = Path("proofs/YM4/CONTINUUM_TRANSFER_PROOF_SHELL.md")
    text = p.read_text()
    assert "## Status" in text
    assert "OPEN" in text
    assert "continuum" in text.lower()
    assert "Blocking lemma" in text
