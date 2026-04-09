import json
from pathlib import Path

def test_anchored_closure_missing_lemma_manifests_are_aligned():
    first = json.loads(
        Path("manifests/anchored_closure_first_missing_lemmas.json").read_text()
    )
    second = json.loads(
        Path("manifests/anchored_closure_second_missing_lemmas.json").read_text()
    )
    third = json.loads(
        Path("manifests/anchored_closure_third_missing_lemmas.json").read_text()
    )

    assert first["file"] == second["file"] == third["file"] == "YMFormal/AnchoredClosure.lean"
    assert first["status"] == second["status"] == third["status"] == "conditional"

    first_axioms = [item["axiom"] for item in first["blockers"]]
    second_axioms = [item["axiom"] for item in second["blockers"]]
    third_axioms = [item["axiom"] for item in third["blockers"]]

    assert first_axioms == second_axioms == third_axioms == [
        "valuation_additivity",
        "lambdaMin_monotone_of_psd_boundary",
        "spectral_contraction_from_anchored_closure",
    ]
