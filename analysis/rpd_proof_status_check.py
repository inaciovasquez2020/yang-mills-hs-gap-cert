from __future__ import annotations

from pathlib import Path

REQUIRED = [
    "proofs/RPD/RPD_PROOF_STATUS_2026_04.yaml",
    "proofs/RPD/RPD_TARGETS_2026_04.md",
    "templates/RPD/RPD_PROOF_SHELLS_2026_04.md",
    "open_problems/RPD_ERROR_GAIN_LEMMA.md",
    "registries/rpd/RPD_AXIOM_MAP_2026_04.yaml",
]

def main() -> None:
    missing = [p for p in REQUIRED if not Path(p).exists()]
    if missing:
        raise SystemExit(f"missing required RPD proof-shell files: {missing}")
    print("PASS: RPD proof-shell files present")

if __name__ == "__main__":
    main()
