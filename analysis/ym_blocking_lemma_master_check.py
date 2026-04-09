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

EXPECTED = {
    "YM-1": "YM1_BLOCKING_LEMMA_OPEN",
    "YM-2": "YM2_BLOCKING_LEMMA_OPEN",
    "YM-3": "YM3_BLOCKING_LEMMA_OPEN",
    "YM-4": "YM4_BLOCKING_LEMMA_OPEN",
    "YM-5": "YM5_BLOCKING_LEMMA_OPEN",
}

OUT = Path("artifacts/ym_blocking_lemma_master_status.json")
MD = Path("proofs/status/YM_BLOCKING_LEMMA_MASTER_STATUS.md")


def main() -> None:
    statuses = {k: json.loads(v.read_text())["status"] for k, v in FILES.items()}
    checks = {k: statuses[k] == EXPECTED[k] for k in FILES}
    payload = {
        "status": "YM_BLOCKING_LEMMA_MASTER_OPEN" if all(checks.values()) else "YM_BLOCKING_LEMMA_MASTER_MISMATCH",
        "statuses": statuses,
        "checks": checks,
        "count_open": sum(bool(v) for v in checks.values()),
        "count_required": len(checks),
    }

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True))

    MD.parent.mkdir(parents=True, exist_ok=True)
    MD.write_text(
        "# YM Blocking Lemma Master Status\n\n"
        f"Status: {payload['status']}\n\n"
        f"Count: {payload['count_open']} / {payload['count_required']}\n\n"
        "## Entries\n"
        + "\n".join(f"- {k}: {statuses[k]} | ok={checks[k]}" for k in FILES)
        + "\n"
    )

    print(payload["status"])
    print(f"count_open={payload['count_open']}")
    print(f"count_required={payload['count_required']}")
    print(OUT)
    print(MD)


if __name__ == "__main__":
    main()
