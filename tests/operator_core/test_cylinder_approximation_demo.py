import subprocess
import sys

p = subprocess.run(
    ["python3","experiments/operator_core/cylinder_approximation_demo.py"],
    capture_output=True,
    text=True
)

if p.returncode != 0:
    sys.exit(1)

print("cylinder approximation demo: PASS")
