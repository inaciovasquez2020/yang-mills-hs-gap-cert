from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def test_ym_frontier_registry_alignment_is_exact() -> None:
    subprocess.run([sys.executable, "analysis/ym_frontier_registry_alignment_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_frontier_registry_alignment.json").read_text())
    assert payload["status"] == "YM_FRONTIER_REGISTRY_ALIGNED"


def test_ym_frontier_registry_alignment_has_same_ids() -> None:
    subprocess.run([sys.executable, "analysis/ym_frontier_registry_alignment_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_frontier_registry_alignment.json").read_text())
    assert payload["frontier_ids"] == payload["registry_ids"]
