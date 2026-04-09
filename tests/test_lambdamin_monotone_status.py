from pathlib import Path
import re

text = Path("YMFormal/AnchoredClosure.lean").read_text()

def test_lambdamin_monotone_still_axiomatic():
    assert re.search(r"\baxiom\s+lambdaMin_monotone_of_psd_boundary\b", text)
    assert not re.search(r"\btheorem\s+lambdaMin_monotone_of_psd_boundary\b", text)
