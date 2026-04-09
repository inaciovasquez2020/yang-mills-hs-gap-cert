from pathlib import Path
import re
import json

text = Path("YMFormal/AnchoredClosure.lean").read_text()

names = [
    "lambdaMin_monotone_of_psd_boundary",
    "spectral_contraction_from_anchored_closure",
]

items = {}
for name in names:
    items[name] = {
        "axiom_present": bool(re.search(rf"\baxiom\s+{re.escape(name)}\b", text)),
        "theorem_present": bool(re.search(rf"\btheorem\s+{re.escape(name)}\b", text)),
    }

remaining = sum(1 for v in items.values() if v["axiom_present"])

out = {
    "file": "YMFormal/AnchoredClosure.lean",
    "status": "conditional" if remaining else "unconditional",
    "conditional_axioms_remaining": remaining,
    "items": items,
}
print(json.dumps(out, indent=2))
