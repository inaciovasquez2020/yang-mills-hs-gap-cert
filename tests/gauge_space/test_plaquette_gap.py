import subprocess
import sys

p = subprocess.run(
    ["python3", "experiments/gauge_space/plaquette_laplacian_demo.py"],
    capture_output=True,
    text=True
)

if p.returncode != 0:
    if __name__ == "__main__":
            sys.exit(1)
ok = True

for line in p.stdout.strip().split("\n"):
    n, gap, scaled = [float(x) for x in line.split()]
    if gap <= 0:
        ok = False
    if scaled <= 0:
        ok = False

if not ok:
    if __name__ == "__main__":
            sys.exit(1)
print("plaquette gap demo: PASS")
