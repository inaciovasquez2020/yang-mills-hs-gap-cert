from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

def test_ym1_blocking_lemma_status_is_open() -> None:
    subprocess.run([sys.executable, "analysis/ym1_blocking_lemma_status_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym1_blocking_lemma_status.json").read_text())
    assert payload["status"] == "YM1_BLOCKING_LEMMA_OPEN"

def test_ym1_blocking_lemma_target_phrase_present() -> None:
    subprocess.run([sys.executable, "analysis/ym1_blocking_lemma_status_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym1_blocking_lemma_status.json").read_text())
    assert payload["checks"]["## Blocking lemma"] is True
