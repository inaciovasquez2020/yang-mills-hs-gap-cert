import subprocess
import sys

p = subprocess.run(
    ["python3","experiments/poincare/path_laplacian_spectrum_test.py"],
    capture_output=True,
    text=True
)

if p.returncode != 0:
    if __name__ == "__main__":
            sys.exit(1)
ok = True

for line in p.stdout.strip().split("\n"):
    L,numeric_gap,analytic_gap,err = [float(x) for x in line.split()]
    if err > 1e-8:
        ok = False

if not ok:
    if __name__ == "__main__":
            sys.exit(1)
print("path Laplacian spectrum test: PASS")
