from pathlib import Path

def test_conditional_unconditional_closure_bodies_note_exists():
    text = Path("proofs/AnchoredClosure/CONDITIONAL_UNCONDITIONAL_CLOSURE_BODIES_2026_04.lean").read_text()
    assert "theorem valuation_additivity" in text
    assert "theorem lambdaMin_monotone_of_psd_boundary" in text
    assert "theorem spectral_contraction_from_anchored_closure" in text
