import json
import subprocess
import sys
from pathlib import Path


def test_rpd_metrics_export() -> None:
    proc = subprocess.run(
        [sys.executable, "analysis/rpd_metrics_export.py"],
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "PASS: RPD metrics exported" in proc.stdout

    p = Path("reports/RPD/RPD_METRICS_2026_04.json")
    assert p.exists()
    data = json.loads(p.read_text())
    assert data["total_theorems"] == 5
    assert "mathematical_proof_completeness_percent" in data
