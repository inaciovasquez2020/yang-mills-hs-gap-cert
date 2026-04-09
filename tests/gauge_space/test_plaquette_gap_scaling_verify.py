import subprocess
import sys

p = subprocess.run(
    ["python3", "experiments/gauge_space/plaquette_gap_scaling_verify.py"],
    capture_output=True,
    text=True
)

if p.returncode != 0:
    raise RuntimeError('gauge-space verification must not execute at import time')

ok = True

for line in p.stdout.strip().split("\n"):
    n, numeric_gap, analytic_gap, lower_bound, err = [float(x) for x in line.split()]
    if err > 1e-10:
        ok = False
    if analytic_gap + 1e-12 < lower_bound:
        ok = False

if not ok:
    if __name__ == "__main__":
    sys.exit(1)

print("plaquette gap scaling verification: PASS")
