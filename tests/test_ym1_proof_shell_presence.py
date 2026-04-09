from pathlib import Path

def test_ym1_proof_shell_present() -> None:
    p = Path("proofs/YM1/NONABELIAN_OPERATOR_PROOF_SHELL.md")
    text = p.read_text()
    assert "## Status" in text
    assert "OPEN" in text
    assert "Blocking lemma" in text
