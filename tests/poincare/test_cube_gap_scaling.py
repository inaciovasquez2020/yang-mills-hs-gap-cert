import subprocess, sys

p = subprocess.run(
    ["python3", "experiments/poincare/cube_laplacian_gap_test.py"],
    capture_output=True,
    text=True
)

lines = p.stdout.strip().split("\n")

ok = True

for line in lines:
    L, gap, val = [float(x) for x in line.split()]
    if val <= 0:
        ok = False

if not ok:
    if __name__ == "__main__":
            sys.exit(1)
print("cube Laplacian scaling test: PASS")
