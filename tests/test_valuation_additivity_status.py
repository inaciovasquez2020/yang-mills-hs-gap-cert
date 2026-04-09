import re
from pathlib import Path


text = Path("YMFormal/AnchoredClosure.lean").read_text()


def test_valuation_additivity_now_theorem():
    assert re.search(r"\btheorem\s+valuation_additivity\b", text)
    assert not re.search(r"\baxiom\s+valuation_additivity\b", text)
