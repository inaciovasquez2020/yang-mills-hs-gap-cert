import json
from pathlib import Path

def test_anchored_closure_second_missing_lemma_manifest():
    manifest = json.loads(
        Path("manifests/anchored_closure_second_missing_lemmas.json").read_text()
    )
    assert manifest["file"] == "YMFormal/AnchoredClosure.lean"
    assert manifest["status"] == "conditional"

    expected = {
        "valuation_additivity": "valuation_on_disjoint_union",
        "lambdaMin_monotone_of_psd_boundary": "dirichlet_psd",
        "spectral_contraction_from_anchored_closure": "spectral_contraction_estimate",
    }

    for item in manifest["blockers"]:
        assert item["axiom"] in expected
        assert item["second_missing_lemma"] == expected[item["axiom"]]
        assert Path(item["proof_shell"]).is_file()
