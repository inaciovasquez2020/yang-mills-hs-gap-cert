from pathlib import Path

def test_block_spectral_gap_status_surface() -> None:
    status = Path("STATUS.md").read_text()
    readme_status = Path("README_STATUS.md").read_text()

    assert "| BLOCK_SPECTRAL_GAP_CORE_LEMMA | OPEN | See open_problems/BLOCK_SPECTRAL_GAP_CORE_LEMMA.md |" in status
    assert "Canonical target file: open_problems/BLOCK_SPECTRAL_GAP_CORE_LEMMA.md" in readme_status
