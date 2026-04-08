from __future__ import annotations

from pathlib import Path


REQUIRED = [
    "proofs/RPD/RPD_TARGETS_2026_04.md",
    "registries/rpd/RPD_AXIOM_MAP_2026_04.yaml",
    "open_problems/RPD_ERROR_GAIN_LEMMA.md",
    "toolkit/RPD/RPD_CLOSURE_CHAIN_2026_04.md",
]


def main() -> None:
    missing = [p for p in REQUIRED if not Path(p).exists()]
    if missing:
        raise SystemExit(f"missing required RPD files: {missing}")
    print("PASS: RPD registry files present")


if __name__ == "__main__":
    main()
