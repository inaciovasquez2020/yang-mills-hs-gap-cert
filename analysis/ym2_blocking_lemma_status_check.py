#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

SRC = Path("proofs/YM2/GAUGE_INVARIANT_COERCIVITY_PROOF_SHELL.md")
OUT = Path("artifacts/ym2_blocking_lemma_status.json")
MD = Path("proofs/YM2/YM2_BLOCKING_LEMMA_STATUS.md")

REQUIRED_PHRASES = [
    "## Status",
    "OPEN",
    "## Blocking lemma",
    "No non-gauge zero mode survives in the physical quotient.",
]

def main() -> None:
    text = SRC.read_text()
    checks = {phrase: (phrase in text) for phrase in REQUIRED_PHRASES}
    payload = {
        "status": "YM2_BLOCKING_LEMMA_OPEN" if all(checks.values()) else "YM2_BLOCKING_LEMMA_SHELL_INCOMPLETE",
        "checks": checks,
        "source": str(SRC),
        "target": "No non-gauge zero mode survives in the physical quotient.",
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True))
    MD.parent.mkdir(parents=True, exist_ok=True)
    MD.write_text(
        "# YM2 Blocking Lemma Status\n\n"
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
