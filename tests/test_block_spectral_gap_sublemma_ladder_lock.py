from pathlib import Path

def test_block_spectral_gap_sublemma_ladder_lock() -> None:
    s = Path("open_problems/BLOCK_SPECTRAL_GAP_SUBLEMMAS.md").read_text()
    assert "Status: OPEN" in s
    assert "## Sublemma 1 — Local Hessian Approximation" in s
    assert "## Sublemma 2 — Local-to-Global Laplacian Comparison" in s
    assert "## Sublemma 3 — Spectral Transfer" in s
    assert "No claim upgrade is permitted unless either the core lemma is discharged or every sublemma above is discharged and their composition is written explicitly." in s
