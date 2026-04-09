from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def test_ym_final_closure_status_is_closed_infrastructure_open_math() -> None:
    subprocess.run([sys.executable, "analysis/ym_final_closure_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_final_closure_status.json").read_text())
    assert payload["status"] == "YM_INFRASTRUCTURE_CLOSED_MATH_OPEN"


def test_ym_final_closure_remaining_counts_are_correct() -> None:
    subprocess.run([sys.executable, "analysis/ym_final_closure_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_final_closure_status.json").read_text())
    assert payload["remaining_infrastructure_steps"] == 0
    assert payload["remaining_math_steps"] == 5
