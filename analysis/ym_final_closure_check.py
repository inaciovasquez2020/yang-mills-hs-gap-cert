#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

FILES = {
    "disproof": Path("artifacts/disproof_of_simulated_mass_gap_proof.json"),
    "missing": Path("artifacts/missing_yang_mills_ingredients.json"),
    "frontier": Path("artifacts/ym_frontier_status.json"),
    "registry": Path("artifacts/ym_proof_shell_registry.json"),
    "open_status": Path("artifacts/ym_proof_shell_status_open.json"),
    "master": Path("artifacts/ym_master_status.json"),
    "alignment": Path("artifacts/ym_frontier_registry_alignment.json"),
}

OUT = Path("artifacts/ym_final_closure_status.json")
MD = Path("proofs/status/YM_FINAL_CLOSURE_STATUS.md")


def read_json(path: Path) -> dict:
    return json.loads(path.read_text())


def main() -> None:
    payloads = {k: read_json(v) for k, v in FILES.items()}

    ok = {
        "disproof": payloads["disproof"]["verdict"] == "DISPROVED_AS_A_YANG_MILLS_MASS_GAP_PROOF",
        "missing": payloads["missing"]["status"] == "OPEN_FRONTIER" and len(payloads["missing"]["missing_ingredients"]) == 5,
        "frontier": payloads["frontier"]["status"] == "OPEN_FRONTIER",
        "registry": payloads["registry"]["status"] == "PROOF_SHELL_REGISTRY_COMPLETE",
        "open_status": payloads["open_status"]["status"] == "ALL_PROOF_SHELLS_OPEN",
        "master": payloads["master"]["status"] == "YM_MASTER_STATUS_CONSISTENT",
        "alignment": payloads["alignment"]["status"] == "YM_FRONTIER_REGISTRY_ALIGNED",
    }

    proof_shell_count = payloads["registry"]["count_present"]
    open_math_frontiers = len(payloads["missing"]["missing_ingredients"])
    infra_remaining = 0 if all(ok.values()) else sum(1 for v in ok.values() if not v)

    final = {
        "status": "YM_INFRASTRUCTURE_CLOSED_MATH_OPEN" if all(ok.values()) else "YM_INFRASTRUCTURE_INCOMPLETE",
        "checks": ok,
        "proof_shell_count": proof_shell_count,
        "open_math_frontiers": open_math_frontiers,
        "remaining_infrastructure_steps": infra_remaining,
        "remaining_math_steps": open_math_frontiers,
        "minimal_remaining_obstruction": (
            "Explicit closure of YM-1 through YM-5."
            if all(ok.values())
            else "Complete failing infrastructure checks first."
        ),
    }

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(final, indent=2, sort_keys=True))

    MD.parent.mkdir(parents=True, exist_ok=True)
    MD.write_text(
        "# YM Final Closure Status\n\n"
        f"Status: {final['status']}\n\n"
        f"- Proof shells present: {final['proof_shell_count']}\n"
        f"- Remaining infrastructure steps: {final['remaining_infrastructure_steps']}\n"
        f"- Remaining math steps: {final['remaining_math_steps']}\n"
        f"- Minimal remaining obstruction: {final['minimal_remaining_obstruction']}\n\n"
        "## Checks\n"
        + "\n".join(f"- {k}: {v}" for k, v in ok.items())
        + "\n"
    )

    print(final["status"])
    print(f"remaining_infrastructure_steps={final['remaining_infrastructure_steps']}")
    print(f"remaining_math_steps={final['remaining_math_steps']}")
    print(OUT)
    print(MD)


if __name__ == "__main__":
    main()
