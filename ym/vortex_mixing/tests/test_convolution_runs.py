import subprocess
import sys
from pathlib import Path

def test_run_script():
    script = Path(__file__).parents[2] / "python" / "convolution_gap.py"
    r = subprocess.run([sys.executable, str(script)], capture_output=True, text=True)
    assert r.returncode == 0
    # Check for expected output patterns
    assert "Convolution Gap Analysis" in r.stdout
    assert "spectral gap" in r.stdout
    assert "L=" in r.stdout
    print(f"Script output:\n{r.stdout}")
