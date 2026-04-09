#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

SOURCES = {
    "frontier": Path("artifacts/ym_frontier_status.json"),
    "registry": Path("artifacts/ym_proof_shell_registry.json"),
    "open_status": Path("artifacts/ym_proof_shell_status_open.json"),
}

OUT = Path("artifacts/ym_master_status.json")
MD = Path("proofs/status/YM_MASTER_STATUS.md")


def read_json(path: Path) -> dict:
    return json.loads(path.read_text())


def main() -> None:
    frontier = read_json(SOURCES["frontier"])
    registry = read_json(SOURCES["registry"])
    open_status = read_json(SOURCES["open_status"])

    payload = {
        "status": (
            "YM_MASTER_STATUS_CONSISTENT"
            if frontier["status"] == "OPEN_FRONTIER"
            and registry["status"] == "PROOF_SHELL_REGISTRY_COMPLETE"
            and open_status["status"] == "ALL_PROOF_SHELLS_OPEN"
            else "YM_MASTER_STATUS_MISMATCH"
        ),
        "frontier_status": frontier["status"],
        "registry_status": registry["status"],
        "open_status": open_status["status"],
        "proof_shell_count": registry["count_present"],
        "proof_shell_required": registry["count_required"],
    }

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True))

    MD.parent.mkdir(parents=True, exist_ok=True)
    MD.write_text(
        "# YM Master Status\n\n"
        f"Status: {payload['status']}\n\n"
        f"- Frontier: {payload['frontier_status']}\n"
        f"- Registry: {payload['registry_status']}\n"
        f"- Open-status: {payload['open_status']}\n"
        f"- Proof shells: {payload['proof_shell_count']} / {payload['proof_shell_required']}\n"
    )

    print(payload["status"])
    print(OUT)
    print(MD)


if __name__ == "__main__":
    main()
