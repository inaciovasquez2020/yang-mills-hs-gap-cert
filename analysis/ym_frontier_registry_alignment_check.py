#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

FRONTIER = Path("artifacts/missing_yang_mills_ingredients.json")
REGISTRY = Path("artifacts/ym_proof_shell_registry.json")
OUT = Path("artifacts/ym_frontier_registry_alignment.json")
MD = Path("proofs/status/YM_FRONTIER_REGISTRY_ALIGNMENT.md")


def main() -> None:
    frontier = json.loads(FRONTIER.read_text())
    registry = json.loads(REGISTRY.read_text())

    frontier_ids = sorted(x["id"] for x in frontier["missing_ingredients"])
    registry_ids = sorted(registry["present"].keys())

    payload = {
        "status": "YM_FRONTIER_REGISTRY_ALIGNED" if frontier_ids == registry_ids else "YM_FRONTIER_REGISTRY_MISMATCH",
        "frontier_ids": frontier_ids,
        "registry_ids": registry_ids,
    }

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True))

    MD.parent.mkdir(parents=True, exist_ok=True)
    MD.write_text(
        "# YM Frontier Registry Alignment\n\n"
        f"Status: {payload['status']}\n\n"
        "## Frontier IDs\n"
        + "\n".join(f"- {x}" for x in frontier_ids)
        + "\n\n## Registry IDs\n"
        + "\n".join(f"- {x}" for x in registry_ids)
        + "\n"
    )

    print(payload["status"])
    print(OUT)
    print(MD)


if __name__ == "__main__":
    main()
