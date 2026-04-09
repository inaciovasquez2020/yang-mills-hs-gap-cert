from pathlib import Path
import re

text = Path("YMFormal/AnchoredClosure.lean").read_text()

def test_spectral_contraction_from_anchored_closure_still_axiomatic():
    assert re.search(r"\baxiom\s+spectral_contraction_from_anchored_closure\b", text)
    assert not re.search(r"\btheorem\s+spectral_contraction_from_anchored_closure\b", text)
