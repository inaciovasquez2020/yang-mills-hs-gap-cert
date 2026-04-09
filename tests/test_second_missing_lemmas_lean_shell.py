from pathlib import Path

def test_second_missing_lemmas_lean_shell_exists():
    text = Path("YMFormal/AnchoredClosure/SecondMissingLemmas.lean").read_text()
    assert "axiom valuation_on_disjoint_union" in text
    assert "axiom dirichlet_psd" in text
    assert "axiom spectral_contraction_estimate" in text
