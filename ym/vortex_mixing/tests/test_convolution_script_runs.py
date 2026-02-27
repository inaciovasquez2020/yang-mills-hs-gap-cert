import subprocess
import sys
from pathlib import Path

def test_script_runs():
    root = Path(__file__).resolve().parents[2]
    # The correct path is ym/python/convolution_gap.py, not ym/vortex_mixing/python/
    script = root / "ym" / "python" / "convolution_gap.py"
    print(f"Looking for script at: {script}")
    assert script.exists(), f"Script not found at {script}"
    
    r = subprocess.run([sys.executable, str(script)], capture_output=True, text=True)
    assert r.returncode == 0, f"Script failed with error: {r.stderr}"
    assert "Convolution Gap Analysis" in r.stdout
    print(f"Script output:\n{r.stdout}")
