from pathlib import Path

def test_block_spectral_gap_sublemma_1_lock() -> None:
    s = Path("open_problems/BLOCK_SPECTRAL_GAP_SUBLEMMA_1_LOCAL_HESSIAN_APPROXIMATION.md").read_text()
    ladder = Path("open_problems/BLOCK_SPECTRAL_GAP_SUBLEMMAS.md").read_text()
    assert "Status: OPEN" in s
    assert "\\sup_U \\left\\|\\nabla^2 S_B(U)-\\beta \\Delta_B\\right\\| \\le C L^{-2}." in s
    assert "## Sublemma 1 — Local Hessian Approximation" in ladder
