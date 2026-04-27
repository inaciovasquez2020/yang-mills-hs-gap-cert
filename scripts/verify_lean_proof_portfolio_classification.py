#!/usr/bin/env python3
from pathlib import Path
import re
import sys

p = Path("docs/status/LEAN_PROOF_PORTFOLIO_CLASSIFICATION.md")
if not p.exists():
    raise SystemExit("missing docs/status/LEAN_PROOF_PORTFOLIO_CLASSIFICATION.md")

text = p.read_text(encoding="utf-8")

required = [
    "Portfolio class:",
    "Allowed description",
    "Forbidden description",
    "Classification rule",
    "Public sentence",
    "must not be described",
]

for needle in required:
    if needle not in text:
        raise SystemExit(f"missing required classification phrase: {needle}")

for forbidden in [
    "solves the Clay problems",
    "proves all major conjectures",
    "theorem-complete proof network",
]:
    if forbidden in text.lower():
        raise SystemExit(f"forbidden overclaim phrase present: {forbidden}")

klass_match = re.search(r"Portfolio class:\s+\*\*(.+?)\*\*", text)
if not klass_match:
    raise SystemExit("missing portfolio class value")

klass = klass_match.group(1)

allowed_classes = {
    "PROOF_FACING",
    "CONDITIONAL_FRONTIER",
    "INFRASTRUCTURE_DOCUMENTATION",
    "LEGACY_SCAFFOLD",
}

if klass not in allowed_classes:
    raise SystemExit(f"unknown portfolio class: {klass}")

print("lean proof portfolio classification: PASS")
