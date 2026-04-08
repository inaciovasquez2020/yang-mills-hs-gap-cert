import subprocess
import sys


def test_rpd_dependency_status_check() -> None:
    proc = subprocess.run(
        [sys.executable, "analysis/rpd_dependency_status_check.py"],
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "PASS: RPD dependency/status propagation verified" in proc.stdout
