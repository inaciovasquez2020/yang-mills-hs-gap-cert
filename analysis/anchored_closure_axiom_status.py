from pathlib import Path
import re
import json

TARGET = Path("YMFormal/AnchoredClosure.lean")
text = TARGET.read_text()

names = [
    "valuation_additivity",
    "lambdaMin_monotone_of_psd_boundary",
    "spectral_contraction_from_anchored_closure",
]

status = {}
for name in names:
    status[name] = {
        "present": bool(re.search(rf"\baxiom\s+{re.escape(name)}\b", text)),
        "theorem_present": bool(re.search(rf"\btheorem\s+{re.escape(name)}\b", text)),
    }

out = {
    "file": str(TARGET),
    "conditional_axioms_remaining": sum(1 for v in status.values() if v["present"]),
    "items": status,
}
print(json.dumps(out, indent=2))
