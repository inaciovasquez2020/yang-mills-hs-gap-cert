from __future__ import annotations

import json
from pathlib import Path

def test_corrected_math_status_is_open() -> None:
    payload = json.loads(Path("artifacts/ym_corrected_math_status_2026_04.json").read_text())
    assert payload["status"] == "YM_INFRASTRUCTURE_CLOSED_MATH_OPEN"
    assert payload["mathematics_closed"] is False

def test_corrected_math_status_counts_are_correct() -> None:
    payload = json.loads(Path("artifacts/ym_corrected_math_status_2026_04.json").read_text())
    assert payload["remaining_math_steps"] == 5
    assert payload["solved_math_frontiers"] == 0
    assert payload["infrastructure_steps_remaining"] == 0
