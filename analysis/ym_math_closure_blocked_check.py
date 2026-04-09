#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

FILES = {
    "YM-1": Path("artifacts/ym1_blocking_lemma_status.json"),
    "YM-2": Path("artifacts/ym2_blocking_lemma_status.json"),
    "YM-3": Path("artifacts/ym3_blocking_lemma_status.json"),
    "YM-4": Path("artifacts/ym4_blocking_lemma_status.json"),
    "YM-5": Path("artifacts/ym5_blocking_lemma_status.json"),
}

OUT = Path("artifacts/ym_math_closure_blocked.json")
MD = Path("proofs/status/YM_MATH_CLOSURE_BLOCKED.md")

def main() -> None:
    statuses = {k: json.loads(v.read_text())["status"] for k, v in FILES.items()}
    payload = {
        "status": "YM_MATH_NOT_SOLVED",
        "blocking_frontiers": list(FILES.keys()),
        "statuses": statuses,
        "required_closures": 5,
        "closed": 0,
    }

    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True))
    MD.write_text(
        "# YM Math Closure Status\n\n"
        "Status: YM_MATH_NOT_SOLVED\n\n"
        "Blocking frontiers: YM-1 … YM-5\n\n"
        + "\n".join(f"- {k}: {v}" for k, v in statuses.items())
        + "\n"
    )

    print(payload["status"])
    print("blocking_frontiers=5")
    print(OUT)
    print(MD)

if __name__ == "__main__":
    main()
