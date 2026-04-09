from pathlib import Path
import re

text = Path("YMFormal/AnchoredClosure.lean").read_text()

def has_axiom(name: str) -> bool:
    return bool(re.search(rf"\baxiom\s+{re.escape(name)}\b", text))

def test_expected_conditional_axioms_present():
    assert has_axiom("valuation_additivity")
    assert has_axiom("lambdaMin_monotone_of_psd_boundary")
    assert has_axiom("spectral_contraction_from_anchored_closure")
