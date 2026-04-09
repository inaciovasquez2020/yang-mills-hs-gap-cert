#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

SRC = Path("proofs/YM5/MASS_GAP_OBSERVABLE_PROOF_SHELL.md")
OUT = Path("artifacts/ym5_blocking_lemma_status.json")
MD = Path("proofs/YM5/YM5_BLOCKING_LEMMA_STATUS.md")

REQUIRED_PHRASES = [
    "## Status",
    "OPEN",
    "## Blocking lemma",
    "A nontrivial gauge-invariant observable exists whose vacuum-subtracted two-point function detects the physical spectral gap.",
]

def main() -> None:
    text = SRC.read_text()
    checks = {phrase: (phrase in text) for phrase in REQUIRED_PHRASES}
    payload = {
        "status": "YM5_BLOCKING_LEMMA_OPEN" if all(checks.values()) else "YM5_BLOCKING_LEMMA_SHELL_INCOMPLETE",
        "checks": checks,
        "source": str(SRC),
        "target": "A nontrivial gauge-invariant observable exists whose vacuum-subtracted two-point function detects the physical spectral gap.",
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True))
    MD.parent.mkdir(parents=True, exist_ok=True)
    MD.write_text(
        "# YM5 Blocking Lemma Status\n\n"
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
