import json
import re
from pathlib import Path


lean_text = Path("YMFormal/AnchoredClosure.lean").read_text()
json_data = json.loads(Path("reports/RPD/RPD_ANCHORED_CLOSURE_FULL_STATUS_2026_04.json").read_text())


def test_full_status_json_matches_current_axiom_count():
    names = [
        "lambdaMin_monotone_of_psd_boundary",
        "spectral_contraction_from_anchored_closure",
    ]
    remaining = sum(
        1 for name in names
        if re.search(rf"\baxiom\s+{re.escape(name)}\b", lean_text)
    )
    assert json_data["status"] == "conditional"
    assert json_data["conditional_axioms_remaining"] == remaining == 2
