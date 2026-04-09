from pathlib import Path

def test_unconditional_closure_dependencies_status():
    text = Path("proofs/AnchoredClosure/UNCONDITIONAL_CLOSURE_DEPENDENCIES_2026_04.md").read_text()
    required = [
        "carrier : AnchoredPatch → Finset Plaquette",
        "carrier_union_law",
        "hessian_decomposition",
        "dirichlet_psd",
        "lambdaMin_def",
        "decompose_main_energy",
        "local_stability_from_coercivity",
    ]
    for item in required:
        assert item in text, item
