import subprocess
import sys

p = subprocess.run(
    ["python3", "experiments/poincare/cube_product_spectrum_compare.py"],
    capture_output=True,
    text=True
)

if p.returncode != 0:
    if __name__ == "__main__":
    sys.exit(1)

ok = True

for line in p.stdout.strip().split("\n"):
    L, numeric_gap, analytic_gap, lower_bound, err = [float(x) for x in line.split()]
    if err > 1e-8:
        ok = False
    if analytic_gap < lower_bound:
        ok = False

if not ok:
    sys.exit(1)

print("cube product spectrum comparison: PASS")
