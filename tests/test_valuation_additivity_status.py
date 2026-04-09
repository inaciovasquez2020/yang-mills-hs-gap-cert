from pathlib import Path
import re

text = Path("YMFormal/AnchoredClosure.lean").read_text()

def test_valuation_additivity_still_axiomatic():
    assert re.search(r"\baxiom\s+valuation_additivity\b", text)
    assert not re.search(r"\btheorem\s+valuation_additivity\b", text)
