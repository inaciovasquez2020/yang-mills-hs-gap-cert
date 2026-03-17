import subprocess
import sys

p = subprocess.run(
    ["python3", "experiments/cycle_localization/plaquette_filling_demo.py"],
    capture_output=True,
    text=True
)

if p.returncode != 0:
    sys.exit(1)

if "boundary matches cycle: True" not in p.stdout:
    sys.exit(1)

print("plaquette filling demo: PASS")
