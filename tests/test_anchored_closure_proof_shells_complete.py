from pathlib import Path

def test_anchored_closure_proof_shells_complete():
    required = [
        "proofs/AnchoredClosure/VALUATION_ADDITIVITY_PROOF_SHELL_2026_04.md",
        "proofs/AnchoredClosure/LAMBDAMIN_MONOTONE_PSD_BOUNDARY_PROOF_SHELL_2026_04.md",
        "proofs/AnchoredClosure/SPECTRAL_CONTRACTION_FROM_ANCHORED_CLOSURE_PROOF_SHELL_2026_04.md",
    ]
    for rel in required:
        assert Path(rel).is_file(), rel
