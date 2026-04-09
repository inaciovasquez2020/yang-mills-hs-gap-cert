import json
from pathlib import Path

def test_anchored_closure_dependency_chains_manifest():
    manifest = json.loads(
        Path("manifests/anchored_closure_dependency_chains.json").read_text()
    )
    assert manifest["file"] == "YMFormal/AnchoredClosure.lean"
    assert manifest["status"] == "conditional"

    expected = {
        "valuation_additivity": [
            "carrier_union_law",
            "valuation_on_disjoint_union",
            "valuation_additivity",
        ],
        "lambdaMin_monotone_of_psd_boundary": [
            "hessian_decomposition",
            "dirichlet_psd",
            "lambdaMin_def",
            "lambdaMin_monotone_of_psd_boundary",
        ],
        "spectral_contraction_from_anchored_closure": [
            "lambdaMin_monotone_of_psd_boundary",
            "local_stability_from_coercivity",
            "spectral_contraction_estimate",
            "spectral_contraction_from_anchored_closure",
        ],
    }

    for item in manifest["chains"]:
        assert item["axiom"] in expected
        assert item["steps"] == expected[item["axiom"]]
        assert Path(item["proof_shell"]).is_file()
