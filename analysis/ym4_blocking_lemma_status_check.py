#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

SRC = Path("proofs/YM4/CONTINUUM_TRANSFER_PROOF_SHELL.md")
OUT = Path("artifacts/ym4_blocking_lemma_status.json")
MD = Path("proofs/YM4/YM4_BLOCKING_LEMMA_STATUS.md")

REQUIRED_PHRASES = [
    "## Status",
    "OPEN",
    "## Blocking lemma",
    "Uniform coercivity is stable under the joint continuum and thermodynamic limit.",
]

def main() -> None:
    text = SRC.read_text()
    checks = {phrase: (phrase in text) for phrase in REQUIRED_PHRASES}
    payload = {
        "status": "YM4_BLOCKING_LEMMA_OPEN" if all(checks.values()) else "YM4_BLOCKING_LEMMA_SHELL_INCOMPLETE",
        "checks": checks,
        "source": str(SRC),
        "target": "Uniform coercivity is stable under the joint continuum and thermodynamic limit.",
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True))
    MD.parent.mkdir(parents=True, exist_ok=True)
    MD.write_text(
        "# YM4 Blocking Lemma Status\n\n"
        f"Status: {payload['status']}\n\n"
        f"Source: {payload['source']}\n\n"
        f"Target: {payload['target']}\n\n"
        "## Checks\n"
        + "\n".join(f"- {k}: {v}" for k, v in checks.items())
        + "\n"
    )
    print(payload["status"])
    print(OUT)
    print(MD)

if __name__ == "__main__":
    main()
