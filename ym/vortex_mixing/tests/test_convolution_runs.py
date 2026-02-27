import subprocess,sys
from pathlib import Path
def test_run_script():
    script=Path(__file__).parents[2]/"python"/"convolution_gap_test.py"
    r=subprocess.run([sys.executable,str(script)],capture_output=True,text=True)
    assert r.returncode==0
    # should print probabilities
    assert "M=" in r.stdout
