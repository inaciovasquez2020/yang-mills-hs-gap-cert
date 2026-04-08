from __future__ import annotations

from pathlib import Path
import sys
import yaml

STATUS_PATH = Path("proofs/RPD/RPD_PROOF_STATUS_2026_04.yaml")
ROOT = Path(".")

ALLOWED = {"open", "partial", "proved", "blocked"}


def fail(msg: str) -> None:
    print(f"FAIL: {msg}")
    raise SystemExit(1)


def main() -> None:
    if not STATUS_PATH.exists():
        fail(f"missing status file: {STATUS_PATH}")

    data = yaml.safe_load(STATUS_PATH.read_text())
    if not isinstance(data, dict):
        fail("status file must be a YAML mapping")

    items = data.get("theorems")
    if not isinstance(items, list) or not items:
        fail("status file must contain nonempty key 'theorems'")

    seen = set()

    for i, item in enumerate(items):
        if not isinstance(item, dict):
            fail(f"theorems[{i}] must be a mapping")

        name = item.get("name")
        status = item.get("status")
        artifact = item.get("artifact")

        if not isinstance(name, str) or not name.strip():
            fail(f"theorems[{i}].name must be nonempty string")
        if name in seen:
            fail(f"duplicate theorem name: {name}")
        seen.add(name)

        if status not in ALLOWED:
            fail(f"{name}: invalid status {status!r}")

        if not isinstance(artifact, str) or not artifact.strip():
            fail(f"{name}: artifact must be nonempty string")

        artifact_path = ROOT / artifact
        if not artifact_path.exists():
            fail(f"{name}: missing artifact path {artifact}")

    print("PASS: RPD proof status consistency verified")


if __name__ == "__main__":
    main()
