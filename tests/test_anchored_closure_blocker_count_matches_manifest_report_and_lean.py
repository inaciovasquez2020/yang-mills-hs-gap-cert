import json
import re
from pathlib import Path

def test_anchored_closure_blocker_count_matches_manifest_report_and_lean():
    lean_text = Path("YMFormal/AnchoredClosure.lean").read_text()
    manifest = json.loads(Path("manifests/anchored_closure_blockers.json").read_text())
    report = json.loads(Path("reports/RPD/RPD_ANCHORED_CLOSURE_FULL_STATUS_2026_04.json").read_text())

    names = [item["name"] for item in manifest["blockers"]]
    lean_count = sum(
        1 for name in names
        if re.search(rf"\baxiom\s+{re.escape(name)}\b", lean_text)
    )

    assert lean_count == 3
    assert len(names) == 3
    assert manifest["status"] == "conditional"
    assert report["status"] == "conditional"
    assert report["conditional_axioms_remaining"] == 3
    assert lean_count == len(names) == report["conditional_axioms_remaining"]
