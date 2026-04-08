from __future__ import annotations

from pathlib import Path
import sys
import yaml

STATUS = Path("proofs/RPD/RPD_PROOF_STATUS_2026_04.yaml")

REQUIRED = {
    "RPD_4_KERNEL_PRESERVATION": "proved",
    "RPD_5A_PULSE_TO_LAMBDAMIN_ZERO": "partial",
    "RPD_5B_ZERO_MODE_TO_NONCOERCIVE": "partial",
    "RPD_6_TWO_BUBBLE_INCOMPATIBILITY": "partial",
    "RPD_ERROR_GAIN_LEMMA": "blocked",
}


def fail(msg: str) -> None:
    print(f"FAIL: {msg}")
    raise SystemExit(1)


def main() -> None:
    data = yaml.safe_load(STATUS.read_text())
    if not isinstance(data, dict):
        fail("status file must be a YAML mapping")
    items = data.get("theorems")
    if not isinstance(items, list):
        fail("status file must contain key 'theorems'")
    got = {}
    for item in items:
        if not isinstance(item, dict):
            fail("each theorem entry must be a mapping")
        name = item.get("name")
        status = item.get("status")
        if isinstance(name, str):
            got[name] = status
    for name, status in REQUIRED.items():
        if got.get(name) != status:
            fail(f"{name}: expected status {status!r}, got {got.get(name)!r}")
    print("PASS: RPD proof-status progress levels verified")


if __name__ == "__main__":
    main()
