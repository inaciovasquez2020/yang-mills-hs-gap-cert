from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

def test_missing_ingredients_report_is_emitted() -> None:
    subprocess.run([sys.executable, "analysis/extract_missing_yang_mills_ingredients.py"], check=True)
    payload = json.loads(Path("artifacts/missing_yang_mills_ingredients.json").read_text())
    assert payload["status"] == "OPEN_FRONTIER"
    assert len(payload["missing_ingredients"]) == 5

def test_missing_ingredients_include_nonabelian_operator_and_continuum_transfer() -> None:
    subprocess.run([sys.executable, "analysis/extract_missing_yang_mills_ingredients.py"], check=True)
    payload = json.loads(Path("artifacts/missing_yang_mills_ingredients.json").read_text())
    ids = {x["id"] for x in payload["missing_ingredients"]}
    assert "YM-1" in ids
    assert "YM-4" in ids
