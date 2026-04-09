from pathlib import Path

def test_third_missing_lemmas_lean_shell_exists():
    text = Path("YMFormal/AnchoredClosure/ThirdMissingLemmas.lean").read_text()
    assert "axiom lambdaMin_def" in text
