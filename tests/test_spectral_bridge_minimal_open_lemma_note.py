from pathlib import Path

def test_spectral_bridge_minimal_open_lemma_note_exists():
    p = Path("proofs/RG/SPECTRAL_BRIDGE_MINIMAL_OPEN_LEMMA_2026_04.md")
    assert p.exists()
    s = p.read_text()
    assert "CONDITIONAL" in s
    assert "SPECTRAL_CONTRACTION_RG" in s
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)\\,E_{\\mathrm{main}}(u)" in s
