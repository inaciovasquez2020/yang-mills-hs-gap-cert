from pathlib import Path
import re
import json

text = Path("YMFormal/AnchoredClosure.lean").read_text()

out = {
    "axiom_present": bool(re.search(r"\baxiom\s+spectral_contraction_from_anchored_closure\b", text)),
    "theorem_present": bool(re.search(r"\btheorem\s+spectral_contraction_from_anchored_closure\b", text)),
    "status": "conditional" if re.search(r"\baxiom\s+spectral_contraction_from_anchored_closure\b", text) else "open"
}
print(json.dumps(out, indent=2))
