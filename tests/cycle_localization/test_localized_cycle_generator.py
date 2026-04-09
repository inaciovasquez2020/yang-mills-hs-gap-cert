import subprocess
import sys

p = subprocess.run(
    ["python3","experiments/cycle_localization/local_cycle_support_demo.py"],
    capture_output=True,
    text=True
)

if p.returncode != 0:
    if __name__ == "__main__":
            sys.exit(1)
print("localized cycle generator demo: PASS")
