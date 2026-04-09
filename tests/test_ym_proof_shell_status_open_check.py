from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def test_all_ym_proof_shells_are_open() -> None:
    subprocess.run([sys.executable, "analysis/ym_proof_shell_status_open_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_proof_shell_status_open.json").read_text())
    assert payload["status"] == "ALL_PROOF_SHELLS_OPEN"


def test_all_ym_proof_shell_status_values_equal_open() -> None:
    subprocess.run([sys.executable, "analysis/ym_proof_shell_status_open_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_proof_shell_status_open.json").read_text())
    assert all(v == "OPEN" for v in payload["statuses"].values())
