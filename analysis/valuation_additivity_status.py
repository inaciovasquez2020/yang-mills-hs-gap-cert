from pathlib import Path
import re
import json

text = Path("YMFormal/AnchoredClosure.lean").read_text()

out = {
    "axiom_present": bool(re.search(r"\baxiom\s+valuation_additivity\b", text)),
    "theorem_present": bool(re.search(r"\btheorem\s+valuation_additivity\b", text)),
    "status": "conditional" if re.search(r"\baxiom\s+valuation_additivity\b", text) else "open"
}
print(json.dumps(out, indent=2))
