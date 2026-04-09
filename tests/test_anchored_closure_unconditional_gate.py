import json
import re
import subprocess
from pathlib import Path

NAMES = [
    "valuation_additivity",
    "lambdaMin_monotone_of_psd_boundary",
    "spectral_contraction_from_anchored_closure",
]

def test_anchored_closure_unconditional_gate():
    lean_text = Path("YMFormal/AnchoredClosure.lean").read_text()
    report = json.loads(Path("reports/RPD/RPD_ANCHORED_CLOSURE_FULL_STATUS_2026_04.json").read_text())
    manifest = json.loads(Path("manifests/anchored_closure_blockers.json").read_text())
    dashboard = json.loads(
        subprocess.check_output(
            ["python3", "analysis/anchored_closure_full_status.py"],
            text=True,
        )
    )

    axiom_count = sum(
        1 for name in NAMES
        if re.search(rf"\baxiom\s+{re.escape(name)}\b", lean_text)
    )
    theorem_count = sum(
        1 for name in NAMES
        if re.search(rf"\btheorem\s+{re.escape(name)}\b", lean_text)
    )

    if axiom_count == 0:
        assert theorem_count == 3
        assert report["status"] == "unconditional"
        assert report["conditional_axioms_remaining"] == 0
        assert manifest["status"] == "unconditional"
        assert len(manifest["blockers"]) == 0
        assert dashboard["status"] == "unconditional"
        assert dashboard["conditional_axioms_remaining"] == 0
    else:
        assert axiom_count == 3
        assert theorem_count == 0
        assert report["status"] == "conditional"
        assert report["conditional_axioms_remaining"] == 3
        assert manifest["status"] == "conditional"
        assert len(manifest["blockers"]) == 3
        assert dashboard["status"] == "conditional"
        assert dashboard["conditional_axioms_remaining"] == 3
