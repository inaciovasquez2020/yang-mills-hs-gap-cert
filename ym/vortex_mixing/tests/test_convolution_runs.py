import subprocess
import sys
from pathlib import Path

def test_run_script():
    root = Path(__file__).resolve().parents[3]
    script = root / "ym" / "vortex_mixing" / "python" / "convolution_gap.py"
    r = subprocess.run([sys.executable, str(script)], capture_output=True, text=True)
    assert r.returncode == 0
    assert "Convolution Gap Analysis" in r.stdout
