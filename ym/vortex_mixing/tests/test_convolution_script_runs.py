import subprocess
import sys
from pathlib import Path

def test_script_runs():
    root = Path(__file__).resolve().parents[2]
    script = root / "ym" / "vortex_mixing" / "python" / "convolution_gap_test.py"
    r = subprocess.run([sys.executable, str(script)], capture_output=True, text=True)
    assert r.returncode == 0
    assert "dev_from_half" in r.stdout
