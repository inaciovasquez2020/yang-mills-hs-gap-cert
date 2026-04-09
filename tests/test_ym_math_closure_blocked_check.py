from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

def test_ym_math_closure_is_not_solved() -> None:
    subprocess.run([sys.executable, "analysis/ym_math_closure_blocked_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_math_closure_blocked.json").read_text())
    assert payload["status"] == "YM_MATH_NOT_SOLVED"

def test_ym_math_closure_has_five_blocking_frontiers() -> None:
    subprocess.run([sys.executable, "analysis/ym_math_closure_blocked_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_math_closure_blocked.json").read_text())
    assert payload["required_closures"] == 5
