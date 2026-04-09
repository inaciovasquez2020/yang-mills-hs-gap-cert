from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

def test_ym_frontier_status_is_open() -> None:
    subprocess.run([sys.executable, "analysis/ym_frontier_status_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_frontier_status.json").read_text())
    assert payload["status"] == "OPEN_FRONTIER"

def test_ym_frontier_registry_contains_all_required_ids() -> None:
    subprocess.run([sys.executable, "analysis/ym_frontier_status_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_frontier_status.json").read_text())
    assert all(payload["present"].values())
