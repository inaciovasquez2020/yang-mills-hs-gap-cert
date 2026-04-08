import subprocess
import sys


def test_rpd_blocking_check() -> None:
    proc = subprocess.run(
        [sys.executable, "analysis/rpd_blocking_check.py"],
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "PASS: RPD blocking graph verified" in proc.stdout
