import json
from pathlib import Path

def test_anchored_closure_first_missing_lemma_manifest():
    manifest = json.loads(
        Path("manifests/anchored_closure_first_missing_lemmas.json").read_text()
    )
    assert manifest["file"] == "YMFormal/AnchoredClosure.lean"
    assert manifest["status"] == "conditional"

    expected = {
        "valuation_additivity": "carrier_union_law",
        "lambdaMin_monotone_of_psd_boundary": "hessian_decomposition",
        "spectral_contraction_from_anchored_closure": "local_stability_from_coercivity",
    }

    for item in manifest["blockers"]:
        assert item["axiom"] in expected
        assert item["first_missing_lemma"] == expected[item["axiom"]]
        assert Path(item["proof_shell"]).is_file()
