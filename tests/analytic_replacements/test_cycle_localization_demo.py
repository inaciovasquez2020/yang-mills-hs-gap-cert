import subprocess,sys

p=subprocess.run(
    ["python3","experiments/analytic_replacements/cycle_localization_demo.py"],
    capture_output=True,
    text=True
)

if p.returncode!=0:
    sys.exit(1)

print("cycle localization demo: PASS")
