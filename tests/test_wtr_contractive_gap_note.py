from pathlib import Path


def test_wtr_contractive_gap_note_exists() -> None:
    p = Path("proofs/RPD/conditional/WTR_CONTRACTIVE_GAP_2026_04.md")
    assert p.exists()


def test_wtr_contractive_gap_note_contains_open_lemma() -> None:
    s = Path("proofs/RPD/conditional/WTR_CONTRACTIVE_GAP_2026_04.md").read_text()
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)\\,E_{\\mathrm{main}}(u)" in s
    assert "Minimal remaining open lemma" in s
