from __future__ import annotations

from pathlib import Path
import sys
import yaml

STATUS = Path("proofs/RPD/RPD_PROOF_STATUS_2026_04.yaml")

ALLOWED = {"open", "partial", "proved", "blocked"}


def fail(msg: str) -> None:
    print(f"FAIL: {msg}")
    raise SystemExit(1)


def main() -> None:
    data = yaml.safe_load(STATUS.read_text())
    if not isinstance(data, dict):
        fail("status file must be a YAML mapping")

    items = data.get("theorems")
    if not isinstance(items, list) or not items:
        fail("status file must contain nonempty key 'theorems'")

    by_name: dict[str, dict] = {}
    for i, item in enumerate(items):
        if not isinstance(item, dict):
            fail(f"theorems[{i}] must be a mapping")
        name = item.get("name")
        status = item.get("status")
        blocking = item.get("blocking", [])
        if not isinstance(name, str) or not name.strip():
            fail(f"theorems[{i}].name must be nonempty string")
        if status not in ALLOWED:
            fail(f"{name}: invalid status {status!r}")
        if not isinstance(blocking, list):
            fail(f"{name}: blocking must be a list")
        by_name[name] = item

    for name, item in by_name.items():
        status = item["status"]
        deps = item.get("blocking", [])
        for dep in deps:
            if dep not in by_name:
                fail(f"{name}: unknown dependency {dep}")
            dep_status = by_name[dep]["status"]

            if status == "proved" and dep_status != "proved":
                fail(f"{name}: proved theorem depends on non-proved dependency {dep}={dep_status}")

            if status == "partial" and dep_status == "blocked":
                fail(f"{name}: partial theorem depends on blocked dependency {dep}")

            if status == "open" and dep_status == "blocked":
                fail(f"{name}: open theorem depends on blocked dependency {dep}")

    print("PASS: RPD dependency/status propagation verified")


if __name__ == "__main__":
    main()
