from pathlib import Path

def test_block_spectral_gap_next_missing_object_2026_04() -> None:
    s = Path("docs/status/BLOCK_SPECTRAL_GAP_NEXT_MISSING_OBJECT_2026_04.md").read_text()
    core = Path("open_problems/BLOCK_SPECTRAL_GAP_CORE_LEMMA.md").read_text()
    ladder = Path("open_problems/BLOCK_SPECTRAL_GAP_SUBLEMMAS.md").read_text()
    assert "Status: OPEN" in s
    assert "\\gamma_B \\ge c L^{-2}." in s
    assert "\\sup_U \\left\\|\\nabla^2 S_B(U)-\\beta \\Delta_B\\right\\| \\le C L^{-2}." in s
    assert "SPECTRAL_CONTRACTION_RG" in s
    assert "Status: OPEN" in core
    assert "Status: OPEN" in ladder
