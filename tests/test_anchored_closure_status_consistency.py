import json
import subprocess
from pathlib import Path

def test_anchored_closure_status_consistency():
    dashboard = json.loads(
        subprocess.check_output(
            ["python3", "analysis/anchored_closure_full_status.py"],
            text=True,
        )
    )
    report = json.loads(
        Path("reports/RPD/RPD_ANCHORED_CLOSURE_FULL_STATUS_2026_04.json").read_text()
    )
    assert dashboard["file"] == report["file"] == "YMFormal/AnchoredClosure.lean"
    assert dashboard["status"] == report["status"] == "conditional"
    assert dashboard["conditional_axioms_remaining"] == report["conditional_axioms_remaining"] == 3
