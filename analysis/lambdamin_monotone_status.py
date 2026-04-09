from pathlib import Path
import re
import json

text = Path("YMFormal/AnchoredClosure.lean").read_text()

out = {
    "axiom_present": bool(re.search(r"\baxiom\s+lambdaMin_monotone_of_psd_boundary\b", text)),
    "theorem_present": bool(re.search(r"\btheorem\s+lambdaMin_monotone_of_psd_boundary\b", text)),
    "status": "conditional" if re.search(r"\baxiom\s+lambdaMin_monotone_of_psd_boundary\b", text) else "open"
}
print(json.dumps(out, indent=2))
