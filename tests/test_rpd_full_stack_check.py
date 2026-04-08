import subprocess
import sys


def test_rpd_full_stack_check() -> None:
    proc = subprocess.run(
        [sys.executable, "analysis/rpd_full_stack_check.py"],
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "PASS: RPD full stack verified" in proc.stdout
