import subprocess
import sys

p = subprocess.run(
    ["python3","experiments/analytic_replacements/block_projection_test.py"],
    capture_output=True,
    text=True
)

if p.returncode != 0:
    if __name__ == "__main__":
            sys.exit(1)
print("block projection operator test: PASS")
