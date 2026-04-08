from pathlib import Path

def test_status_mentions_spectral_contraction_rg_as_conditional():
    s = Path("STATUS.md").read_text()
    assert "SPECTRAL_CONTRACTION_RG | CONDITIONAL" in s

def test_minimal_open_lemma_note_matches_status_target():
    s = Path("proofs/RG/SPECTRAL_BRIDGE_MINIMAL_OPEN_LEMMA_2026_04.md").read_text()
    assert "upgrade" in s
    assert "`SPECTRAL_CONTRACTION_RG`" in s
