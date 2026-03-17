import subprocess
import sys

p = subprocess.run(
    ["python3","experiments/analytic_replacements/block_variance_test.py"],
    capture_output=True,
    text=True
)

if p.returncode != 0:
    sys.exit(1)

print("block variance experiment: PASS")
