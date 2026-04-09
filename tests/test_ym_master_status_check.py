from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def test_ym_master_status_is_consistent() -> None:
    subprocess.run([sys.executable, "analysis/ym_master_status_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_master_status.json").read_text())
    assert payload["status"] == "YM_MASTER_STATUS_CONSISTENT"


def test_ym_master_status_counts_all_proof_shells() -> None:
    subprocess.run([sys.executable, "analysis/ym_master_status_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_master_status.json").read_text())
    assert payload["proof_shell_count"] == 5
    assert payload["proof_shell_required"] == 5
