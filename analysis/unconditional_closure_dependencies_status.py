from pathlib import Path
import json

p = Path("proofs/AnchoredClosure/UNCONDITIONAL_CLOSURE_DEPENDENCIES_2026_04.md")
text = p.read_text()

targets = [
    "carrier : AnchoredPatch → Finset Plaquette",
    "carrier_union_law",
    "hessian_decomposition",
    "dirichlet_psd",
    "lambdaMin_def",
    "decompose_main_energy",
    "local_stability_from_coercivity",
]

out = {
    "file": str(p),
    "all_targets_listed": all(t in text for t in targets),
    "targets": {t: (t in text) for t in targets},
    "status": "conditional",
}
print(json.dumps(out, indent=2))
