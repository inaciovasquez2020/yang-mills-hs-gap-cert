import subprocess
import sys

p = subprocess.run(
    ["python3", "experiments/cycle_localization/cube_complex_filling_demo.py"],
    capture_output=True,
    text=True
)

if p.returncode != 0:
    sys.exit(1)

if "bounded radius witness: True" not in p.stdout:
    sys.exit(1)

print("cube complex filling demo: PASS")
