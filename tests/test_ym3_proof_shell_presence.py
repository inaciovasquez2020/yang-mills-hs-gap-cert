from pathlib import Path

def test_ym3_proof_shell_present() -> None:
    p = Path("proofs/YM3/REFLECTION_POSITIVITY_BRIDGE_PROOF_SHELL.md")
    text = p.read_text()
    assert "## Status" in text
    assert "OPEN" in text
    assert "reflection positivity" in text.lower()
    assert "Blocking lemma" in text
