import subprocess
import sys


def test_rpd_manifest_status_sync_check() -> None:
    proc = subprocess.run(
        [sys.executable, "analysis/rpd_manifest_status_sync_check.py"],
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "PASS: RPD manifest/status theorem names synchronized" in proc.stdout
