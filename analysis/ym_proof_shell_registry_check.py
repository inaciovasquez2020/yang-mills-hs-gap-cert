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

OUT = Path("artifacts/ym_proof_shell_registry.json")
MD = Path("proofs/status/YM_PROOF_SHELL_REGISTRY.md")


def main() -> None:
    present = {k: p.exists() for k, p in SHELLS.items()}
    status = "PROOF_SHELL_REGISTRY_COMPLETE" if all(present.values()) else "PROOF_SHELL_REGISTRY_INCOMPLETE"
    payload = {
        "status": status,
        "present": present,
        "count_present": sum(bool(v) for v in present.values()),
        "count_required": len(SHELLS),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True))
    MD.parent.mkdir(parents=True, exist_ok=True)
    MD.write_text(
        "# YM Proof Shell Registry\n\n"
        f"Status: {status}\n\n"
        f"Count: {payload['count_present']} / {payload['count_required']}\n\n"
        "## Entries\n"
        + "\n".join(f"- {k}: {present[k]}" for k in SHELLS)
        + "\n"
    )
    print(status)
    print(OUT)
    print(MD)


if __name__ == "__main__":
    main()
