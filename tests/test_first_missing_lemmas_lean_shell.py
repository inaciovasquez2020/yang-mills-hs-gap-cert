from pathlib import Path

def test_first_missing_lemmas_lean_shell_exists():
    text = Path("YMFormal/AnchoredClosure/FirstMissingLemmas.lean").read_text()
    assert "axiom carrier_union_law" in text
    assert "axiom hessian_decomposition" in text
    assert "axiom local_stability_from_coercivity" in text
