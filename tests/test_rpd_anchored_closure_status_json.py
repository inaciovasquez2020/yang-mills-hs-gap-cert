import json
from pathlib import Path

def test_rpd_anchored_closure_status_json():
    data = json.loads(Path("reports/RPD/RPD_ANCHORED_CLOSURE_STATUS_2026_04.json").read_text())
    assert data["status"] == "conditional"
    assert data["conditional_axioms_remaining"] == 3
    assert data["axioms"] == [
        "valuation_additivity",
        "lambdaMin_monotone_of_psd_boundary",
        "spectral_contraction_from_anchored_closure",
    ]
