import json
from pathlib import Path

def test_anchored_closure_third_missing_lemma_manifest():
    manifest = json.loads(
        Path("manifests/anchored_closure_third_missing_lemmas.json").read_text()
    )
    assert manifest["file"] == "YMFormal/AnchoredClosure.lean"
    assert manifest["status"] == "conditional"

    expected = {
        "valuation_additivity": "valuation_additivity",
        "lambdaMin_monotone_of_psd_boundary": "lambdaMin_def",
        "spectral_contraction_from_anchored_closure": "spectral_contraction_from_anchored_closure",
    }

    for item in manifest["blockers"]:
        assert item["axiom"] in expected
        assert item["third_missing_lemma"] == expected[item["axiom"]]
        assert Path(item["proof_shell"]).is_file()
