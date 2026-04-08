from __future__ import annotations

from pathlib import Path
import sys
import yaml

STATUS = Path("proofs/RPD/RPD_PROOF_STATUS_2026_04.yaml")


def fail(msg: str) -> None:
    print(f"FAIL: {msg}")
    raise SystemExit(1)


def main() -> None:
    if not STATUS.exists():
        fail(f"missing file: {STATUS}")

    data = yaml.safe_load(STATUS.read_text())
    if not isinstance(data, dict):
        fail("status file must be a YAML mapping")

    items = data.get("theorems")
    if not isinstance(items, list) or not items:
        fail("status file must contain nonempty key 'theorems'")

    names = []
    by_name = {}
    for i, item in enumerate(items):
        if not isinstance(item, dict):
            fail(f"theorems[{i}] must be a mapping")
        name = item.get("name")
        if not isinstance(name, str) or not name.strip():
            fail(f"theorems[{i}].name must be nonempty string")
        if name in by_name:
            fail(f"duplicate theorem name: {name}")
        by_name[name] = item
        names.append(name)

    for name in names:
        blocking = by_name[name].get("blocking")
        if not isinstance(blocking, list):
            fail(f"{name}: blocking must be a list")
        for dep in blocking:
            if not isinstance(dep, str) or not dep.strip():
                fail(f"{name}: blocking entries must be nonempty strings")
            if dep not in by_name:
                fail(f"{name}: unknown blocking dependency {dep}")

    print("PASS: RPD blocking graph verified")


if __name__ == "__main__":
    main()
