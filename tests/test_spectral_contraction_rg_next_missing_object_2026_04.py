from pathlib import Path

def test_spectral_contraction_rg_next_missing_object_2026_04() -> None:
    s = Path("docs/status/SPECTRAL_CONTRACTION_RG_NEXT_MISSING_OBJECT_2026_04.md").read_text()
    status = Path("STATUS.md").read_text()
    bridge = Path("proofs/RG/SPECTRAL_BRIDGE_MINIMAL_OPEN_LEMMA_2026_04.md").read_text()
    assert "Status: OPEN" in s
    assert "SPECTRAL_CONTRACTION_RG" in s
    assert "BLOCK_SPECTRAL_GAP_CORE_LEMMA" in s
    assert "YM_MASS_GAP_ROUTE_CERTIFICATE_2026" in s
    assert "SPECTRAL_CONTRACTION_RG | CONDITIONAL" in status
    assert "SPECTRAL_CONTRACTION_RG" in bridge
