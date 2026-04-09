import re
from pathlib import Path


text = Path("YMFormal/AnchoredClosure.lean").read_text()


def has_axiom(name: str) -> bool:
    return re.search(rf"\baxiom\s+{re.escape(name)}\b", text) is not None


def has_theorem(name: str) -> bool:
    return re.search(rf"\btheorem\s+{re.escape(name)}\b", text) is not None


def test_expected_conditional_axioms_present():
    assert not has_axiom("valuation_additivity")
    assert has_theorem("valuation_additivity")
    assert has_axiom("lambdaMin_monotone_of_psd_boundary")
    assert has_axiom("spectral_contraction_from_anchored_closure")
