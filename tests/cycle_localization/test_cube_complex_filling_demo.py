import subprocess
import sys

p = subprocess.run(
    ["python3", "experiments/cycle_localization/cube_complex_filling_demo.py"],
    capture_output=True,
    text=True
)

if p.returncode != 0:
    if __name__ == "__main__":
            sys.exit(1)
if "bounded radius witness: True" not in p.stdout:
    if __name__ == "__main__":
            sys.exit(1)
print("cube complex filling demo: PASS")
