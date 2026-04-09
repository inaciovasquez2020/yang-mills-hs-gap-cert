#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

SHELLS = {
    "YM-1": Path("proofs/YM1/NONABELIAN_OPERATOR_PROOF_SHELL.md"),
    "YM-2": Path("proofs/YM2/GAUGE_INVARIANT_COERCIVITY_PROOF_SHELL.md"),
    "YM-3": Path("proofs/YM3/REFLECTION_POSITIVITY_BRIDGE_PROOF_SHELL.md"),
    "YM-4": Path("proofs/YM4/CONTINUUM_TRANSFER_PROOF_SHELL.md"),
    "YM-5": Path("proofs/YM5/MASS_GAP_OBSERVABLE_PROOF_SHELL.md"),
}

OUT = Path("artifacts/ym_proof_shell_status_open.json")
MD = Path("proofs/status/YM_PROOF_SHELL_STATUS_OPEN.md")


def shell_status(path: Path) -> str | None:
    text = path.read_text()
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if line.strip() == "## Status" and i + 1 < len(lines):
            return lines[i + 1].strip()
    return None


def main() -> None:
    statuses = {k: shell_status(p) for k, p in SHELLS.items()}
    all_open = all(v == "OPEN" for v in statuses.values())
    payload = {
        "status": "ALL_PROOF_SHELLS_OPEN" if all_open else "PROOF_SHELL_STATUS_MISMATCH",
        "statuses": statuses,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True))
    MD.parent.mkdir(parents=True, exist_ok=True)
    MD.write_text(
        "# YM Proof Shell Status Open Check\n\n"
        f"Status: {payload['status']}\n\n"
        "## Entries\n"
        + "\n".join(f"- {k}: {statuses[k]}" for k in SHELLS)
        + "\n"
    )
    print(payload["status"])
    print(OUT)
    print(MD)


if __name__ == "__main__":
    main()
