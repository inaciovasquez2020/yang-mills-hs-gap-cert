from pathlib import Path

def test_anchored_closure_first_missing_lemmas_are_recorded():
    valuation = Path(
        "proofs/AnchoredClosure/VALUATION_ADDITIVITY_PROOF_SHELL_2026_04.md"
    ).read_text()
    lambdamin = Path(
        "proofs/AnchoredClosure/LAMBDAMIN_MONOTONE_PSD_BOUNDARY_PROOF_SHELL_2026_04.md"
    ).read_text()
    spectral = Path(
        "proofs/AnchoredClosure/SPECTRAL_CONTRACTION_FROM_ANCHORED_CLOSURE_PROOF_SHELL_2026_04.md"
    ).read_text()

    assert "lemma carrier_union_law" in valuation
    assert "lemma hessian_decomposition" in lambdamin
    assert "lemma local_stability_from_coercivity" in spectral
