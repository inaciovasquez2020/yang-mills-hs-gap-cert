from pathlib import Path

def test_block_spectral_gap_core_lemma_lock() -> None:
    p = Path("open_problems/BLOCK_SPECTRAL_GAP_CORE_LEMMA.md")
    s = p.read_text()
    assert "Status: OPEN" in s
    assert "sup_U \\left\\|\\nabla^2 S_B(U)-\\beta \\Delta_B\\right\\| \\le C L^{-2}." in s
    assert "\\gamma_B \\ge c L^{-2}." in s
    assert "No claim upgrade is permitted unless this lemma is discharged or reduced to a strictly weaker explicit sublemma." in s
