import json
from pathlib import Path


def test_anchored_closure_manifest_matches_report():
    manifest = json.loads(Path("manifests/anchored_closure_blockers.json").read_text())
    report = json.loads(Path("reports/RPD/RPD_ANCHORED_CLOSURE_FULL_STATUS_2026_04.json").read_text())

    manifest_names = [item["name"] for item in manifest["blockers"]]
    report_names = report["axioms"]

    assert manifest["status"] == report["status"] == "conditional"
    assert manifest["file"] == report["file"] == "YMFormal/AnchoredClosure.lean"
    assert manifest_names == report_names
    assert len(manifest_names) == report["conditional_axioms_remaining"] == 2
    assert manifest_names == [
        "lambdaMin_monotone_of_psd_boundary",
        "spectral_contraction_from_anchored_closure",
    ]
