from pathlib import Path


def test_wtr_refined_coercive_contraction_note_exists() -> None:
    p = Path("proofs/RPD/conditional/WTR_REFINED_COERCIVE_CONTRACTION_2026_04.md")
    assert p.exists()


def test_wtr_refined_coercive_contraction_note_is_conditional() -> None:
    s = Path("proofs/RPD/conditional/WTR_REFINED_COERCIVE_CONTRACTION_2026_04.md").read_text()
    assert "conditional closure statement" in s
    assert "It does not by itself constitute an unconditional proof of the Yang--Mills mass gap." in s
    assert "Set" in s and "\\eta := 1 - \\frac{C\\,\\epsilon_0}{\\beta c_\\Delta}" in s
