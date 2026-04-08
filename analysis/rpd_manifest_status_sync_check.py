from __future__ import annotations

from pathlib import Path
import sys
import yaml

MANIFEST = Path("manifests/RPD/RPD_TARGET_MANIFEST_2026_04.yaml")
STATUS = Path("proofs/RPD/RPD_PROOF_STATUS_2026_04.yaml")


def fail(msg: str) -> None:
    print(f"FAIL: {msg}")
    raise SystemExit(1)


def load_yaml(path: Path):
    if not path.exists():
        fail(f"missing file: {path}")
    data = yaml.safe_load(path.read_text())
    if not isinstance(data, dict):
        fail(f"{path} must contain a YAML mapping")
    return data


def extract_manifest_names(data: dict) -> set[str]:
    items = data.get("theorems")
    if not isinstance(items, list) or not items:
        fail("manifest must contain nonempty key 'theorems'")
    out: set[str] = set()
    for i, item in enumerate(items):
        if not isinstance(item, dict):
            fail(f"manifest theorems[{i}] must be a mapping")
        name = item.get("name")
        if not isinstance(name, str) or not name.strip():
            fail(f"manifest theorems[{i}].name must be nonempty string")
        out.add(name)
    return out


def extract_status_names(data: dict) -> set[str]:
    items = data.get("theorems")
    if not isinstance(items, list) or not items:
        fail("status file must contain nonempty key 'theorems'")
    out: set[str] = set()
    for i, item in enumerate(items):
        if not isinstance(item, dict):
            fail(f"status theorems[{i}] must be a mapping")
        name = item.get("name")
        if not isinstance(name, str) or not name.strip():
            fail(f"status theorems[{i}].name must be nonempty string")
        out.add(name)
    return out


def main() -> None:
    manifest_names = extract_manifest_names(load_yaml(MANIFEST))
    status_names = extract_status_names(load_yaml(STATUS))

    only_manifest = sorted(manifest_names - status_names)
    only_status = sorted(status_names - manifest_names)

    if only_manifest:
        fail(f"names only in manifest: {only_manifest}")
    if only_status:
        fail(f"names only in status: {only_status}")

    print("PASS: RPD manifest/status theorem names synchronized")


if __name__ == "__main__":
    main()
