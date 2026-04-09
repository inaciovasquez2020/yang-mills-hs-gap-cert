from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def test_ym_blocking_lemma_master_status_is_open() -> None:
    subprocess.run([sys.executable, "analysis/ym_blocking_lemma_master_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_blocking_lemma_master_status.json").read_text())
    assert payload["status"] == "YM_BLOCKING_LEMMA_MASTER_OPEN"


def test_ym_blocking_lemma_master_counts_all_five() -> None:
    subprocess.run([sys.executable, "analysis/ym_blocking_lemma_master_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_blocking_lemma_master_status.json").read_text())
    assert payload["count_open"] == 5
    assert payload["count_required"] == 5
