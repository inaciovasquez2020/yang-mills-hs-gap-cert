import json
import re
from pathlib import Path

def test_anchored_closure_cannot_be_marked_unconditional_while_axioms_remain():
    lean_text = Path("YMFormal/AnchoredClosure.lean").read_text()
    report = json.loads(Path("reports/RPD/RPD_ANCHORED_CLOSURE_FULL_STATUS_2026_04.json").read_text())
    names = [
        "valuation_additivity",
        "lambdaMin_monotone_of_psd_boundary",
        "spectral_contraction_from_anchored_closure",
    ]
    remaining = sum(
        1 for name in names
        if re.search(rf"\baxiom\s+{re.escape(name)}\b", lean_text)
    )
    assert remaining == 3
    assert report["conditional_axioms_remaining"] == remaining
    assert report["status"] == "conditional"
