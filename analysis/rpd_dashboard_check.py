from __future__ import annotations

from pathlib import Path

REQUIRED = [
    "reports/RPD/RPD_STATUS_DASHBOARD_2026_04.md",
    "manifests/RPD/RPD_TARGET_MANIFEST_2026_04.yaml",
    "proofs/RPD/theorems/RPD_4_KERNEL_PRESERVATION.md",
    "proofs/RPD/theorems/RPD_5A_PULSE_TO_LAMBDAMIN_ZERO.md",
    "proofs/RPD/theorems/RPD_5B_ZERO_MODE_TO_NONCOERCIVE.md",
    "proofs/RPD/theorems/RPD_6_TWO_BUBBLE_INCOMPATIBILITY.md",
    "proofs/RPD/theorems/RPD_ERROR_GAIN_LEMMA.md",
]

def main() -> None:
    missing = [p for p in REQUIRED if not Path(p).exists()]
    if missing:
        raise SystemExit(f"missing required RPD dashboard files: {missing}")
    print("PASS: RPD dashboard files present")

if __name__ == "__main__":
    main()
