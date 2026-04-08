import subprocess
import sys


def test_rpd_status_consistency_check() -> None:
    proc = subprocess.run(
        [sys.executable, "analysis/rpd_status_consistency_check.py"],
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "PASS: RPD proof status consistency verified" in proc.stdout
