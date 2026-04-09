#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

SRC = Path("artifacts/missing_yang_mills_ingredients.json")
OUT = Path("artifacts/ym_frontier_status.json")
MD = Path("proofs/status/YM_FRONTIER_STATUS.md")

REQUIRED_IDS = ["YM-1", "YM-2", "YM-3", "YM-4", "YM-5"]

def main() -> None:
    payload = json.loads(SRC.read_text())
    ids = [x["id"] for x in payload["missing_ingredients"]]
    present = {k: (k in ids) for k in REQUIRED_IDS}
    status = {
        "status": "OPEN_FRONTIER" if all(present.values()) else "INCOMPLETE_FRONTIER_REGISTRY",
        "required_ids": REQUIRED_IDS,
        "present": present,
        "source_status": payload["status"],
        "source_verdict": payload["source_verdict"],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(status, indent=2, sort_keys=True))
    MD.parent.mkdir(parents=True, exist_ok=True)
    MD.write_text(
        "# YM Frontier Status\n\n"
        f"Status: {status['status']}\n\n"
        f"Source status: {status['source_status']}\n\n"
        f"Source verdict: {status['source_verdict']}\n\n"
        "## Registry\n"
        + "\n".join(f"- {k}: {present[k]}" for k in REQUIRED_IDS)
        + "\n"
    )
    print(status["status"])
    print(OUT)
    print(MD)

if __name__ == "__main__":
    main()
